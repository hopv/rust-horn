use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use rustc_middle::mir::{BasicBlock as BB, Field as FldIdx};
use rustc_middle::ty::subst::InternalSubsts as Substs;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind as TyK, VariantDef as VrtDef};
use rustc_target::abi::VariantIdx as VrtIdx;

use std::fmt::{Display, Formatter, Result as FResult};

use crate::analyze::data::{BinOp, Cond, Const, End, Expr, Path, UnOp, Var};
use crate::analyze::{FunDef, PivotDef, Rule, Summary};
use crate::prettify::pr_name;
use crate::util::{
  enumerate_fld_defs, fun_of_fun_ty, has_any_type, only_ty, substs_of_fun_ty, Cap, FLD0, FLD1, VRT0,
};

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
impl<T> Display for Rep<&mut T>
where
  T: Copy,
  Rep<T>: Display,
{
  fn fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", rep(*self.unrep)) }
}

/* name */

fn rep_name(def_id: DefId) -> String { format!("%{}", pr_name(def_id).replace("::", "/")) }

fn safe_ty(ty: Ty) -> String {
  rep(ty).to_string().replace(" ", ".").replace("(", "").replace(")", "")
}

pub fn rep_fun_name(fun_ty: Ty) -> String {
  format!("{}{}", rep_name(fun_of_fun_ty(fun_ty)), rep(substs_of_fun_ty(fun_ty)))
}
fn rep_fun_name_pivot(fun_name: &str, pivot: Option<BB>) -> String {
  if let Some(bb) = pivot {
    format!("{}.{}", fun_name, bb.index())
  } else {
    format!("{}", fun_name)
  }
}
pub fn rep_drop_name(ty: Ty) -> String { format!("drop<{}>", safe_ty(ty)) }

fn rep_adt_name(adt_def: &AdtDef) -> String {
  assert!(!adt_def.is_box());
  rep_name(adt_def.did)
}
fn rep_adt_builder_name(adt_def: &AdtDef, vrt_idx: VrtIdx) -> String {
  assert!(!adt_def.is_box());
  format!("{}-{}", rep_adt_name(adt_def), vrt_idx.index())
}
fn rep_adt_selector_name(adt_def: &AdtDef, vrt_idx: VrtIdx, fld_idx: FldIdx) -> String {
  assert!(!adt_def.is_box());
  format!("{}-{}.{}", rep_adt_name(adt_def), vrt_idx.index(), fld_idx.index())
}
fn rep_builder(base_ty: Ty, vrt_idx: VrtIdx) -> String {
  match &base_ty.kind {
    TyK::Ref(_, ty, Mutability::Mut) => {
      assert!(vrt_idx == VRT0);
      format!("~mut<{}>", rep(ty))
    }
    TyK::Adt(adt_def, substs) => {
      let name = rep_adt_builder_name(adt_def, vrt_idx);
      if !has_any_type(substs) {
        name
      } else {
        format!("(as {} {})", name, rep(base_ty))
      }
    }
    TyK::Tuple(substs) => {
      assert!(vrt_idx == VRT0);
      format!("~tup{}", rep(substs))
    }
    _ => panic!("unexpected type {} for projection", base_ty),
  }
}
fn rep_selector_name(base_ty: Ty, vrt_idx: VrtIdx, fld_idx: FldIdx) -> String {
  match &base_ty.kind {
    TyK::Ref(_, ty, Mutability::Mut) => {
      assert!(vrt_idx == VRT0);
      match fld_idx {
        FLD0 => format!("~cur<{}>", rep(ty)),
        FLD1 => format!("~ret<{}>", rep(ty)),
        _ => panic!("unexpected field {} for a mutable reference", fld_idx.index()),
      }
    }
    TyK::Adt(adt_def, _) => rep_adt_selector_name(adt_def, vrt_idx, fld_idx),
    TyK::Tuple(substs) => {
      assert!(vrt_idx == VRT0);
      format!("~at{}/{}", fld_idx.index(), rep(substs))
    }
    _ => panic!("unexpected type {} for projection", base_ty),
  }
}

/* type */

struct RepAdtTy<'tcx> {
  adt_def: &'tcx AdtDef,
  substs: &'tcx Substs<'tcx>,
}
fn rep_adt_ty<'tcx>(adt_def: &'tcx AdtDef, substs: &'tcx Substs<'tcx>) -> impl Display + 'tcx {
  RepAdtTy { adt_def, substs }
}
impl Display for RepAdtTy<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepAdtTy { adt_def, substs } = *self;
    if has_any_type(substs) {
      write!(f, "({}", rep_adt_name(adt_def))?;
      for ty in substs.types() {
        write!(f, " {}", rep(ty))?;
      }
      write!(f, ")")
    } else {
      write!(f, "{}", rep_adt_name(adt_def))
    }
  }
}
impl Display for Rep<Ty<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let ty = self.unrep;
    match &ty.kind {
      TyK::Bool => write!(f, "Bool"),
      TyK::Int(_) | TyK::Uint(_) => write!(f, "Int"),
      TyK::Float(_) => write!(f, "Real"),
      TyK::Adt(adt_def, substs) => {
        if adt_def.is_box() {
          write!(f, "{}", rep(only_ty(substs)))
        } else {
          write!(f, "{}", rep_adt_ty(adt_def, substs))
        }
      }
      TyK::Ref(_, ty, Mutability::Not) => write!(f, "{}", rep(ty)),
      TyK::Ref(_, ty, Mutability::Mut) => write!(f, "~Mut<{}>", rep(ty)),
      TyK::Tuple(substs) => write!(f, "~Tup{}", rep(substs)),
      TyK::Param(param_ty) => write!(f, "%{}", param_ty.name),
      _ => panic!("unsupported type {}", ty),
    }
  }
}

impl Display for Rep<&Substs<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let substs = self.unrep;
    if has_any_type(substs) {
      write!(f, "<")?;
      let mut sep = "";
      for ty in substs.types() {
        write!(f, "{}{}", sep, safe_ty(ty))?;
        sep = "-";
      }
      write!(f, ">")?;
    }
    Ok(())
  }
}

/* adt definition */

struct RepVrt<'tcx> {
  adt_def: &'tcx AdtDef,
  vrt_idx: VrtIdx,
  vrt_def: &'tcx VrtDef,
  tcx: TyCtxt<'tcx>,
}
fn rep_vrt<'tcx>(
  adt_def: &'tcx AdtDef, vrt_idx: VrtIdx, vrt_def: &'tcx VrtDef, tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
  RepVrt { adt_def, vrt_idx, vrt_def, tcx }
}
impl Display for RepVrt<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepVrt { adt_def, vrt_idx, vrt_def, tcx } = *self;
    let fld_defs = &vrt_def.fields;
    if fld_defs.len() == 0 {
      write!(f, "{}", rep_adt_builder_name(adt_def, vrt_idx))
    } else {
      write!(f, "({}", rep_adt_builder_name(adt_def, vrt_idx))?;
      let substs = Substs::identity_for_item(tcx, vrt_def.def_id);
      for (fld_idx, fld_def) in enumerate_fld_defs(fld_defs) {
        let ty = fld_def.ty(tcx, substs);
        write!(f, " ({} {})", rep_adt_selector_name(adt_def, vrt_idx, fld_idx), rep(ty))?;
      }
      write!(f, ")")?;
      Ok(())
    }
  }
}
struct RepAdt<'tcx> {
  adt_def: &'tcx AdtDef,
  tcx: TyCtxt<'tcx>,
}
fn rep_adt<'tcx>(adt_def: &'tcx AdtDef, tcx: TyCtxt<'tcx>) -> impl Display + 'tcx {
  RepAdt { adt_def, tcx }
}
impl Display for RepAdt<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepAdt { adt_def, tcx } = *self;
    let params = tcx
      .generics_of(adt_def.did)
      .params
      .iter()
      .map(|param_def| param_def.name)
      .collect::<Vec<_>>();
    write!(f, "(declare-datatypes (({} {})) ((par (", rep_adt_name(adt_def), params.len())?;
    let mut sep = "";
    for param in params.iter() {
      write!(f, "{}%{}", sep, param)?;
      sep = " ";
    }
    write!(f, ") (")?;
    for (vrt_idx, vrt_def) in adt_def.variants.iter_enumerated() {
      write!(f, "\n  {}", rep_vrt(adt_def, vrt_idx, vrt_def, tcx))?;
    }
    writeln!(f, "))))")
  }
}

struct RepTup<'tcx> {
  substs: &'tcx Substs<'tcx>,
}
fn rep_tup<'tcx>(substs: &'tcx Substs<'tcx>) -> impl Display + 'tcx { RepTup { substs } }
impl Display for RepTup<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepTup { substs } = self;
    write!(f, "(declare-datatypes ((~Tup{} 0)) ((par () (", rep(substs))?;
    let types = substs.types().collect::<Vec<_>>();
    if types.len() == 0 {
      write!(f, "~tup{}", rep(substs))?;
    } else {
      write!(f, "(~tup{}", rep(substs))?;
      for (i, ty) in types.iter().enumerate() {
        write!(f, " (~at{}/{} {})", i, rep(substs), rep(ty))?;
      }
      write!(f, ")")?;
    }
    writeln!(f, "))))")
  }
}

struct RepMut<'tcx> {
  ty: Ty<'tcx>,
}
fn rep_mut<'tcx>(ty: Ty<'tcx>) -> impl Display + 'tcx { RepMut { ty } }
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
      Var::Input(local) => write!(f, "_{}", local.index()),
      Var::SelfResult => write!(f, "_@"),
      Var::SelfPanic => write!(f, "_!"),
      Var::CallResult(bb) => write!(f, "_@.{}", bb.index()),
      Var::Rand(bb) => write!(f, "_?.{}", bb.index()),
      Var::MutRet(bb, i) => write!(f, "_*.{}_{}", bb.index(), i),
      Var::Split(bb, vrt_idx, fld_idx) => {
        write!(f, "_$.{}_{}/{}", bb.index(), vrt_idx.index(), fld_idx.index())
      }
      Var::Nonce(None) => unreachable!("nonce should have an index for rep"),
      Var::Nonce(Some(i)) => write!(f, "_%.{}", i),
    }
  }
}
impl Display for Rep<&Path<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let path = self.unrep;
    match path {
      Path::Var(var, _) => write!(f, "{}", rep(var)),
      Path::Proj(base_ty, vrt_idx, fld_idx, box path) => {
        write!(f, "({} {})", rep_selector_name(base_ty, *vrt_idx, *fld_idx), rep(path))
      }
    }
  }
}
impl Display for Rep<Const> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let cnst = self.unrep;
    match cnst {
      Const::Bool(b) => write!(f, "{}", b),
      Const::Int(n) => write!(f, "{}", n),
      Const::Real(a) => write!(f, "{}", a),
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
          BinOp::Add => "+",
          BinOp::Sub => "-",
          BinOp::Mul => "*",
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
      Expr::Aggr(ty, vrt_idx, flds) => {
        if flds.len() == 0 {
          write!(f, "{}", rep_builder(ty, *vrt_idx))
        } else {
          write!(f, "({}", rep_builder(ty, *vrt_idx))?;
          for fld in flds.iter() {
            write!(f, " {}", rep(fld))?;
          }
          write!(f, ")")
        }
      }
    }
  }
}

struct RepApply<'a, 'tcx> {
  fun_name: &'a str,
  args: &'a Vec<Expr<'tcx>>,
}
fn rep_apply<'a, 'tcx>(
  fun_name: &'a str, args: &'a Vec<Expr<'tcx>>,
) -> impl Display + Cap<'tcx> + 'a {
  RepApply { fun_name, args }
}
impl Display for RepApply<'_, '_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepApply { fun_name, args } = *self;
    if args.len() == 0 {
      write!(f, "{}", fun_name)
    } else {
      write!(f, "({}", fun_name)?;
      for arg in args.iter() {
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
      Cond::Drop { ty, arg } => write!(f, "({} {})", rep_drop_name(ty), rep(arg)),
      Cond::Eq { tgt, src } => write!(f, "(= {} {})", rep(tgt), rep(src)),
      Cond::Call { fun_ty, args } => write!(f, "{}", rep_apply(&rep_fun_name(fun_ty), args)),
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
      End::Pivot { pivot, args } => {
        write!(f, "{}", rep_apply(&rep_fun_name_pivot(fun_name, Some(*pivot)), args))
      }
      End::Return { res } => {
        if fun_name == &"%main" {
          assert!(res.is_none());
          write!(f, "(= _! false)")
        } else {
          if let Some(expr) = res {
            write!(f, "(= _@ {})", rep(expr))
          } else {
            write!(f, "true")
          }
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
  fun_def: &'a FunDef<'tcx>,
}
fn rep_fun_sig<'a, 'tcx: 'a>(
  fun_name: &'a str, fun_def: &'a FunDef<'tcx>,
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
  fun_name: &'a str, fun_def: &'a FunDef<'tcx>,
) -> impl Display + Cap<'tcx> + 'a {
  RepFunDef { fun_name, fun_def }
}
impl Display for RepFunDef<'_, '_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepFunDef { fun_name, fun_def } = self;
    if fun_def.len() > 0 {
      writeln!(f)?;
    }
    for (pivot, PivotDef { rules, .. }) in fun_def.iter() {
      if let Some(bb) = pivot {
        writeln!(f, "; {} bb{}", fun_name, bb.index())?;
      } else {
        writeln!(f, "; {}", fun_name)?;
      }
      for Rule { vars, args, conds, end } in rules.iter() {
        write!(f, "(assert (forall (")?;
        if vars.len() > 0 {
          let mut sep = "";
          for (var, ty) in vars.iter() {
            write!(f, "{}({} {})", sep, rep(var), rep(ty))?;
            sep = " ";
          }
        } else {
          write!(f, "(_% Int)")?; // dummy
        }
        write!(f, ") (=>\n  (and")?;
        for cond in conds.iter() {
          write!(f, " {}", rep(cond))?;
        }
        writeln!(f, " {})", rep_end(fun_name, end))?;
        writeln!(f, "  {})))", rep_apply(&rep_fun_name_pivot(fun_name, *pivot), args))?;
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
  summary: &'a Summary<'tcx>, tcx: TyCtxt<'tcx>,
) -> impl Display + Cap<'tcx> + 'a {
  RepSummary { summary, tcx }
}
impl Display for RepSummary<'_, '_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let RepSummary { summary: Summary { fun_defs, drop_defs, adt_asks, tup_asks, mut_asks }, tcx } =
      self;
    writeln!(f, "(set-logic HORN)")?;
    // adt definitions
    if adt_asks.len() > 0 {
      writeln!(f)?;
    }
    for &adt_id in adt_asks.iter() {
      write!(f, "{}", rep_adt(tcx.adt_def(adt_id), *tcx))?;
    }
    // muts
    if mut_asks.len() > 0 {
      writeln!(f)?;
    }
    for (_, ty) in mut_asks.iter() {
      write!(f, "{}", rep_mut(ty))?;
    }
    // tuples
    if tup_asks.len() > 0 {
      writeln!(f)?;
    }
    for (_, substs) in tup_asks.iter() {
      write!(f, "{}", rep_tup(substs))?;
    }
    // drop definitions
    if drop_defs.len() > 0 {
      writeln!(f)?;
    }
    for (drop_name, drop_def) in drop_defs.iter() {
      write!(f, "{}", rep_fun_sig(drop_name, drop_def))?;
    }
    for (drop_name, drop_def) in drop_defs.iter() {
      write!(f, "{}", rep_fun_def(drop_name, drop_def))?;
    }
    // functions
    if fun_defs.len() > 0 {
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
