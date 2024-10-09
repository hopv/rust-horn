use std::fmt::{Display, Formatter, Result as FResult};

use crate::analyze::data::{BinOp, Cond, Const, End, Expr, Float, Int, Path, Proj, UnOp, Var};
use crate::analyze::{FunDef, FunDefRef, Pivot, PivotDef, Rule, Summary};
use crate::library;
use crate::prettify::pr_name;
use crate::types::{
    with_tcx, AdtDef, DefId, FieldIdx, FunTy, GenericArgs, GenericArgsRef, Mutability, Ty, TyCtxt,
    TyKind, Tys, VariantDef, VariantIdx,
};
use crate::util::{has_any_type, Cap, FLD0, FLD1, VRT0};

/* basic */

pub struct Rep<T> {
    unrep: T,
}
pub fn rep<T>(x: T) -> Rep<T> { Rep { unrep: x } }
impl<T> Display for Rep<&T>
where
    T: Copy,
    Rep<T>: Display,
{
    fn fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", rep(*self.unrep)) }
}

/* name */

fn rep_name(def_id: DefId) -> String { format!("%{}", pr_name(def_id).replace("::", "/")) }

fn safe_ty(ty: Ty) -> String {
    rep(ty)
        .to_string()
        .replace(' ', ".")
        .replace(['(', ')'], "")
}

pub fn rep_fun_name(fun_ty: FunTy) -> String {
    // FIXME: def_path_str is not suitable for a trait invocation
    // which can be determined at compile-time.
    format!(
        "{}{}",
        rep_name(fun_ty.def_id),
        rep_ty_list(fun_ty.generic_args_ref.types())
    )
}

fn rep_fun_name_pivot(fun_name: &str, pivot: Pivot) -> String {
    if let Pivot::Switch(bb) = pivot {
        format!("{}.{}", fun_name, bb.index())
    } else {
        fun_name.to_string()
    }
}
pub fn rep_drop_name(ty: Ty) -> String { format!("drop<{}>", safe_ty(ty)) }

fn rep_adt_name(adt_def: AdtDef) -> String {
    assert!(!adt_def.is_box());
    rep_name(adt_def.did())
}
fn rep_adt_builder_name(adt_def: AdtDef, variant_index: VariantIdx) -> String {
    assert!(!adt_def.is_box());
    format!("{}-{}", rep_adt_name(adt_def), variant_index.index())
}
fn rep_adt_selector_name(
    adt_def: AdtDef,
    variant_index: VariantIdx,
    field_index: FieldIdx,
) -> String {
    assert!(!adt_def.is_box());
    format!(
        "{}-{}.{}",
        rep_adt_name(adt_def),
        variant_index.index(),
        field_index.index()
    )
}
fn rep_builder(base_ty: Ty, variant_index: VariantIdx) -> String {
    match base_ty.kind() {
        TyKind::Ref(_, ty, Mutability::Mut) => {
            assert!(variant_index == VRT0);
            format!("~mut<{}>", rep(ty))
        }
        TyKind::Adt(adt_def, generic_args) => {
            let name = rep_adt_builder_name(*adt_def, variant_index);
            if has_any_type(generic_args) {
                format!("(as {} {})", name, rep(base_ty))
            } else {
                name
            }
        }
        TyKind::Tuple(types) => {
            assert!(variant_index == VRT0);
            format!("~tup{}", rep_ty_list(types.into_iter()))
        }
        _ => panic!("unexpected type {} for projection", base_ty),
    }
}
fn rep_selector_name(base_ty: Ty, variant_index: VariantIdx, field_index: FieldIdx) -> String {
    match base_ty.kind() {
        TyKind::Ref(_, ty, Mutability::Mut) => {
            assert!(variant_index == VRT0);
            match field_index {
                FLD0 => format!("~cur<{}>", rep(ty)),
                FLD1 => format!("~ret<{}>", rep(ty)),
                _ => panic!(
                    "unexpected field {} for a mutable reference",
                    field_index.index()
                ),
            }
        }
        TyKind::Adt(adt_def, _) => rep_adt_selector_name(*adt_def, variant_index, field_index),
        TyKind::Tuple(types) => {
            assert!(variant_index == VRT0);
            format!(
                "~at{}/{}",
                field_index.index(),
                rep_ty_list(types.into_iter())
            )
        }
        _ => panic!("unexpected type {} for projection", base_ty),
    }
}

/* type */

struct RepAdtTy<'tcx> {
    adt_def: AdtDef<'tcx>,
    generic_args: GenericArgsRef<'tcx>,
}
fn rep_adt_ty<'tcx>(
    adt_def: AdtDef<'tcx>,
    generic_args: GenericArgsRef<'tcx>,
) -> impl Display + 'tcx {
    RepAdtTy {
        adt_def,
        generic_args,
    }
}
impl Display for RepAdtTy<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepAdtTy {
            adt_def,
            generic_args,
        } = *self;
        if has_any_type(generic_args) {
            write!(f, "({}", rep_adt_name(adt_def))?;
            for ty in generic_args.types() {
                write!(f, " {}", rep(ty))?;
            }
            write!(f, ")")
        } else {
            write!(f, "{}", rep_adt_name(adt_def))
        }
    }
}
impl Display for Rep<Ty<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { rep(self.unrep.ty).fmt(f) }
}
impl Display for Rep<rustc_middle::ty::Ty<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let ty = self.unrep;
        match ty.kind() {
            TyKind::Bool => write!(f, "Bool"),
            TyKind::Int(_) | TyKind::Uint(_) => write!(f, "Int"),
            TyKind::Float(_) => write!(f, "Real"),
            TyKind::Adt(adt_def, generic_args) => {
                if let Some(ty) = Ty::new(ty).as_boxed_ty() {
                    write!(f, "{}", rep(ty))
                } else if let Some(alternative) =
                    with_tcx(|tcx| library::need_to_rename_ty(tcx, adt_def.did()))
                {
                    write!(f, "{}", alternative.name)
                } else {
                    write!(f, "{}", rep_adt_ty(*adt_def, generic_args))
                }
            }
            TyKind::Ref(_, ty, Mutability::Not) => write!(f, "{}", rep(ty)),
            TyKind::Ref(_, ty, Mutability::Mut) => write!(f, "~Mut<{}>", rep(ty)),
            TyKind::Tuple(types) => write!(f, "~Tup{}", rep_ty_list(types.into_iter())),
            TyKind::Param(param_ty) => write!(f, "%{}", param_ty.name),
            _ => panic!("unsupported type {}", ty),
        }
    }
}

pub struct RepTyList<'tcx> {
    inner: Vec<rustc_middle::ty::Ty<'tcx>>,
}
pub fn rep_ty_list<'tcx>(
    ty_list: impl Iterator<Item = rustc_middle::ty::Ty<'tcx>>,
) -> impl Display + 'tcx {
    RepTyList {
        inner: ty_list.collect(),
    }
}

impl Display for RepTyList<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let types = &self.inner;
        if !types.is_empty() {
            write!(f, "<")?;
            let mut sep = "";
            for ty in types {
                write!(f, "{}{}", sep, safe_ty(Ty::new(*ty)))?;
                sep = "-";
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

/* adt definition */

struct RepVrt<'tcx> {
    adt_def: AdtDef<'tcx>,
    variant_index: VariantIdx,
    variant_def: &'tcx VariantDef,
    tcx: TyCtxt<'tcx>,
}
fn rep_vrt<'tcx>(
    adt_def: AdtDef<'tcx>,
    variant_index: VariantIdx,
    variant_def: &'tcx VariantDef,
    tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
    RepVrt {
        adt_def,
        variant_index,
        variant_def,
        tcx,
    }
}
impl Display for RepVrt<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepVrt {
            adt_def,
            variant_index,
            variant_def,
            tcx,
        } = *self;
        let fld_defs = &variant_def.fields;
        if fld_defs.is_empty() {
            write!(f, "{}", rep_adt_builder_name(adt_def, variant_index))
        } else {
            write!(f, "({}", rep_adt_builder_name(adt_def, variant_index))?;
            let generic_args = GenericArgs::identity_for_item(tcx, variant_def.def_id);
            for (field_index, fld_def) in fld_defs
                .iter()
                .enumerate()
                .map(|(i, fld_def)| (FieldIdx::from(i), fld_def))
            {
                let ty = fld_def.ty(tcx, generic_args);
                write!(
                    f,
                    " ({} {})",
                    rep_adt_selector_name(adt_def, variant_index, field_index),
                    rep(ty)
                )?;
            }
            write!(f, ")")?;
            Ok(())
        }
    }
}
struct RepAdt<'tcx> {
    adt_def: AdtDef<'tcx>,
    tcx: TyCtxt<'tcx>,
}
fn rep_adt<'tcx>(adt_def: AdtDef<'tcx>, tcx: TyCtxt<'tcx>) -> impl Display + 'tcx {
    RepAdt { adt_def, tcx }
}
impl Display for RepAdt<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepAdt { adt_def, tcx } = *self;
        let params = tcx
            .generics_of(adt_def.did())
            .own_params
            .iter()
            .map(|param_def| param_def.name)
            .collect::<Vec<_>>();
        write!(
            f,
            "(declare-datatypes (({} {})) ((par (",
            rep_adt_name(adt_def),
            params.len()
        )?;
        let mut sep = "";
        for param in &params {
            write!(f, "{}%{}", sep, param)?;
            sep = " ";
        }
        write!(f, ") (")?;
        for (variant_index, variant_def) in adt_def.variants().iter_enumerated() {
            write!(
                f,
                "\n  {}",
                rep_vrt(adt_def, variant_index, variant_def, tcx)
            )?;
        }
        writeln!(f, "))))")
    }
}

struct RepTup<'tcx> {
    generic_args: Tys<'tcx>,
}
fn rep_tup(types: Tys<'_>) -> impl Display + '_ {
    RepTup {
        generic_args: types,
    }
}
impl Display for RepTup<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepTup { generic_args } = self;
        let rep_ty_list = rep_ty_list(generic_args.into_iter());
        write!(f, "(declare-datatypes ((~Tup{} 0)) ((par () (", rep_ty_list)?;
        let types = generic_args.into_iter().collect::<Vec<_>>();
        if types.is_empty() {
            write!(f, "~tup{}", rep_ty_list)?;
        } else {
            write!(f, "(~tup{}", rep_ty_list)?;
            for (i, ty) in types.iter().enumerate() {
                write!(f, " (~at{}/{} {})", i, rep_ty_list, rep(ty))?;
            }
            write!(f, ")")?;
        }
        writeln!(f, "))))")
    }
}

struct RepMut<'tcx> {
    ty: Ty<'tcx>,
}
fn rep_mut(ty: Ty<'_>) -> impl Display + '_ { RepMut { ty } }
impl Display for RepMut<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepMut { ty } = self;
        writeln!(
      f,
      "(declare-datatypes ((~Mut<{}> 0)) ((par () ((~mut<{}> (~cur<{}> {}) (~ret<{}> {}))))))",
      rep(ty),
      rep(ty),
      rep(ty),
      rep(ty),
      rep(ty),
      rep(ty)
    )
    }
}

/* expression */

impl Display for Rep<Var> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let var = self.unrep;
        match var {
            Var::Input { local } => write!(f, "_{}", local.index()),
            Var::SelfResult => write!(f, "_@"),
            Var::SelfPanic => write!(f, "_!"),
            Var::CallResult { caller: bb } => write!(f, "_@.{}", bb.index()),
            Var::CallIdent {
                identifier,
                caller: bb,
            } => write!(f, "_@{identifier}.{}", bb.index()),
            Var::Rand { caller: bb } => write!(f, "_?.{}", bb.index()),
            Var::MutRet {
                location: bb,
                stmt_index: i,
            } => write!(f, "_*.{}_{}", bb.index(), i),
            Var::Split(bb, variant_index, field_index) => {
                write!(
                    f,
                    "_$.{}_{}/{}",
                    bb.index(),
                    variant_index.index(),
                    field_index.index()
                )
            }
            Var::Uninit => {
                // variable names must be unique, but this situation should not happen thanks to the type system
                write!(f, "_%.nonce")
            }
        }
    }
}
impl Display for Rep<&Path<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let path = self.unrep;
        match path {
            Path::Var(var, _) => write!(f, "{}", rep(var)),
            Path::Proj {
                projection:
                    Proj {
                        base_ty,
                        variant_index,
                        field_index,
                    },
                body: box path,
            } => {
                write!(
                    f,
                    "({} {})",
                    rep_selector_name(*base_ty, *variant_index, *field_index),
                    rep(path)
                )
            }
        }
    }
}
impl Display for Rep<Const> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let cnst = self.unrep;
        match cnst {
            Const::Bool(b) => write!(f, "{b}"),
            Const::Int(Int::Int(int)) => write!(f, "{int}"),
            Const::Int(Int::Uint(uint)) => write!(f, "{uint}"),
            Const::Decimal(Float::F16(f16)) => write!(f, "{f16}"),
            Const::Decimal(Float::F32(f32)) => write!(f, "{f32}"),
            Const::Decimal(Float::F64(f64)) => write!(f, "{f64}"),
            Const::Decimal(Float::F128(f128)) => write!(f, "{f128}"),
            Const::Unit => write!(f, "~tup0"),
        }
    }
}
impl Display for Rep<&Expr<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let expr = self.unrep;
        match expr {
            Expr::Path(path) => write!(f, "{}", rep(path)),
            Expr::Const(cnst) => write!(f, "{}", rep(cnst)),
            Expr::BinOp(bin_op, box expr1, box expr2) => {
                let name = match bin_op {
                    BinOp::Add | BinOp::AddWithOverflow => "+",
                    BinOp::Sub | BinOp::SubWithOverflow => "-",
                    BinOp::Mul | BinOp::MulWithOverflow => "*",
                    BinOp::DivInt => "div",
                    BinOp::Mod => "mod",
                    BinOp::DivReal => "/",
                    BinOp::And => "and",
                    BinOp::Eq => "=",
                    BinOp::Lt => "<",
                    BinOp::Le => "<=",
                    BinOp::Ne => panic!(),
                    BinOp::Ge => ">=",
                    BinOp::Gt => ">",
                };
                write!(f, "({} {} {})", name, rep(expr1), rep(expr2))
            }
            Expr::UnOp(un_op, box expr) => {
                let name = match un_op {
                    UnOp::Neg => "-",
                    UnOp::Not => "not",
                    UnOp::Abs => "abs",
                };
                write!(f, "({} {})", name, rep(expr))
            }
            Expr::Aggregate {
                ty,
                variant_index,
                fields,
            } => {
                if fields.is_empty() {
                    write!(f, "{}", rep_builder(*ty, *variant_index))
                } else {
                    write!(f, "({}", rep_builder(*ty, *variant_index))?;
                    for fld in fields.iter() {
                        write!(f, " {}", rep(fld))?;
                    }
                    write!(f, ")")
                }
            }
            Expr::Construct { name, args } => write!(f, "{}", rep_apply(name, args)),
        }
    }
}

struct RepApply<'a, 'tcx> {
    fun_name: &'a str,
    args: &'a [Expr<'tcx>],
}
fn rep_apply<'a, 'tcx>(fun_name: &'a str, args: &'a [Expr<'tcx>]) -> impl Display + Cap<'tcx> + 'a {
    RepApply { fun_name, args }
}
impl Display for RepApply<'_, '_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepApply { fun_name, args } = *self;
        if args.is_empty() {
            write!(f, "{}", fun_name)
        } else {
            write!(f, "({}", fun_name)?;
            for arg in args {
                write!(f, " {}", rep(arg))?;
            }
            write!(f, ")")
        }
    }
}

/* tree */

impl Display for Rep<&Cond<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let cond = self.unrep;
        match cond {
            Cond::Drop { ty, arg } => write!(f, "({} {})", rep_drop_name(*ty), rep(arg)),
            Cond::Eq { tgt, src } => write!(f, "(= {} {})", rep(tgt), rep(src)),
            Cond::Neq { tgt, srcs } => {
                write!(f, "(distinct {}", rep(tgt))?;
                for src in srcs {
                    write!(f, " {}", rep(src))?;
                }
                write!(f, ")")
            }
            Cond::CallRustFn { fun_ty, args } => {
                write!(f, "{}", rep_apply(&rep_fun_name(*fun_ty), args))
            }
            Cond::Intrinsic { name, args } => {
                write!(f, "{}", rep_apply(name, args))
            }
        }
    }
}

struct RepEnd<'a, 'tcx> {
    fun_name: &'a str,
    end: &'a End<'tcx>,
}
fn rep_end<'a, 'tcx: 'a>(fun_name: &'a str, end: &'a End<'tcx>) -> impl Display + Cap<'tcx> + 'a {
    RepEnd { fun_name, end }
}
impl Display for RepEnd<'_, '_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepEnd { fun_name, end } = self;
        match end {
            End::Pivot {
                next_switch: pivot,
                args,
            } => {
                write!(
                    f,
                    "{}",
                    rep_apply(&rep_fun_name_pivot(fun_name, Pivot::Switch(*pivot)), args)
                )
            }
            End::Return { res } => {
                if fun_name == &"%main" {
                    write!(f, "(= _! false)")
                } else if let Some(expr) = res {
                    let r = format!("{}", rep(expr));
                    if r == "~tup0" {
                        write!(f, "true")
                    } else {
                        write!(f, "(= _@ {})", r)
                    }
                } else {
                    write!(f, "true")
                }
            }
            End::Panic => {
                assert!(fun_name == &"%main");
                write!(f, "(= _! true)")
            }
            End::NeverReturn => write!(f, "false"),
        }
    }
}

/* function signature */

struct RepFunSig<'a, 'tcx> {
    fun_name: &'a str,
    fun_def: FunDefRef<'a, 'tcx>,
}
fn rep_fun_sig<'a, 'tcx: 'a>(
    fun_name: &'a str,
    fun_def: FunDefRef<'a, 'tcx>,
) -> impl Display + Cap<'tcx> + 'a {
    RepFunSig { fun_name, fun_def }
}
impl Display for RepFunSig<'_, '_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepFunSig { fun_name, fun_def } = self;
        for (pivot, PivotDef { param_tys, .. }) in fun_def.iter() {
            write!(f, "(declare-fun {} (", rep_fun_name_pivot(fun_name, *pivot))?;
            let mut sep = "";
            for param_ty in param_tys.iter() {
                write!(f, "{}{}", sep, rep(param_ty))?;
                sep = " ";
            }
            writeln!(f, ") Bool)")?;
        }
        Ok(())
    }
}

/* function definition */

struct RepFunDef<'a, 'tcx> {
    fun_name: &'a str,
    fun_def: &'a FunDef<'tcx>,
}
fn rep_fun_def<'a, 'tcx: 'a>(
    fun_name: &'a str,
    fun_def: &'a FunDef<'tcx>,
) -> impl Display + Cap<'tcx> + 'a {
    RepFunDef { fun_name, fun_def }
}
impl Display for RepFunDef<'_, '_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepFunDef { fun_name, fun_def } = self;
        if !fun_def.is_empty() {
            writeln!(f)?;
        }
        for (pivot, PivotDef { rules, .. }) in fun_def.iter() {
            if let Pivot::Switch(bb) = pivot {
                writeln!(f, "; {} bb{}", fun_name, bb.index())?;
            } else {
                writeln!(f, "; {}", fun_name)?;
            }
            for Rule {
                vars,
                args,
                conds,
                end,
            } in rules.iter()
            {
                write!(f, "(assert (forall (")?;
                if vars.is_empty() {
                    write!(f, "(_% Int)")?; // dummy
                } else {
                    let mut sep = "";
                    for (var, ty) in vars.iter() {
                        write!(f, "{}({} {})", sep, rep(var), rep(ty))?;
                        sep = " ";
                    }
                }
                write!(f, ") (=>\n  (and")?;
                for cond in conds.iter() {
                    write!(f, " {}", rep(cond))?;
                }
                writeln!(f, " {})", rep_end(fun_name, end))?;
                writeln!(
                    f,
                    "  {})))",
                    rep_apply(&rep_fun_name_pivot(fun_name, *pivot), args)
                )?;
            }
        }
        Ok(())
    }
}

/* summary */

struct RepSummary<'a, 'tcx> {
    summary: &'a Summary<'tcx>,
    tcx: TyCtxt<'tcx>,
}
pub fn rep_summary<'a, 'tcx: 'a>(
    summary: &'a Summary<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> impl Display + Cap<'tcx> + 'a {
    RepSummary { summary, tcx }
}
impl Display for RepSummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let RepSummary {
            summary:
                Summary {
                    fun_defs,
                    drop_defs,
                    adt_asks,
                    tup_asks,
                    mut_asks,
                },
            tcx,
        } = self;
        writeln!(f, "(set-logic HORN)")?;
        // adt definitions
        if !adt_asks.is_empty() {
            writeln!(f)?;
        }
        for &adt_id in adt_asks.iter() {
            write!(f, "{}", rep_adt(tcx.adt_def(adt_id), *tcx))?;
        }
        // muts
        if !mut_asks.is_empty() {
            writeln!(f)?;
        }
        for (_, ty) in mut_asks.iter() {
            write!(f, "{}", rep_mut(*ty))?;
        }
        // tuples
        if !tup_asks.is_empty() {
            writeln!(f)?;
        }
        for (_, generic_args) in tup_asks.iter() {
            write!(f, "{}", rep_tup(generic_args))?;
        }
        // drop definitions
        if !drop_defs.is_empty() {
            writeln!(f)?;
        }
        for (drop_name, drop_def) in drop_defs.iter() {
            write!(f, "{}", rep_fun_sig(drop_name, drop_def))?;
        }
        for (drop_name, drop_def) in drop_defs.iter() {
            write!(f, "{}", rep_fun_def(drop_name, drop_def))?;
        }
        for chc_defs in library::activated_chc_defs() {
            writeln!(f, "{}", chc_defs.raw)?;
        }

        // functions
        if !fun_defs.is_empty() {
            writeln!(f)?;
        }
        for (fun_name, fun_def) in fun_defs.iter() {
            write!(f, "{}", rep_fun_sig(fun_name, fun_def))?;
        }
        for (fun_name, fun_def) in fun_defs.iter() {
            write!(f, "{}", rep_fun_def(fun_name, fun_def))?;
        }
        // the verification condition
        writeln!(f, "\n(assert (forall ((_% Int)) (=> (%main true) false)))")?;
        writeln!(f, "(check-sat)")?;
        Ok(())
    }
}
