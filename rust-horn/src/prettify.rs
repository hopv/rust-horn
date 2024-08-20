use std::fmt::{Display, Formatter, Result as FResult};
use std::str::pattern::Pattern;

use crate::types::{
    with_tcx, AdtDef, AggregateKind, BasicBlock, BorrowKind, ClosureKind, DefId, FieldIdx, FnSig,
    GenericArgs, Local, LocalDecl, MirBinOp, MirBody, MirUnOp, Mutability, NullOp, Operand,
    ParamEnv, Place, ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    Ty, TyConst, TyCtxt, TyKind, VariantIdx,
};
use crate::util::{enumerate_bbds, get_terminator};

pub fn pr_name(def_id: DefId) -> String {
    with_tcx(|tcx| tcx.def_path_str(def_id)).replace("{{closure}}", "{clsr}")
}

pub fn pr_fun_name(fun: DefId) -> String {
    let name = pr_name(fun);
    match name.as_str() {
        "rand" => "<rand>".to_string(),
        "alloc::alloc::box_free" => "<free>".to_string(),
        "std::io::_print" => "<print>".to_string(),
        "std::mem::swap" => "<swap>".to_string(),
        "std::rt::begin_panic" => "<panic>".to_string(),
        "std::intrinsics::discriminant_value" => "<tag>".to_string(),
        "std::ops::Fn::call" => "<call>".to_string(),
        _ if "std::fmt".is_prefix_of(&name) => "<fmt>".to_string(),
        _ => name,
    }
}

pub struct Pr<T> {
    unpr: T,
}
pub fn pr<T>(x: T) -> Pr<T> { Pr { unpr: x } }
impl<T> Display for Pr<&T>
where
    T: Copy,
    Pr<T>: Display,
{
    fn fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", Pr { unpr: *self.unpr }) }
}
impl<T> Display for Pr<&mut T>
where
    T: Copy,
    Pr<T>: Display,
{
    fn fmt(&self, f: &mut Formatter) -> FResult { write!(f, "{}", pr(*self.unpr)) }
}

impl Display for Pr<FnSig<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let fn_sig = self.unpr;
        write!(f, "(")?;
        let mut sep = "";
        for ty in fn_sig.inputs() {
            write!(f, "{}{}", sep, pr(ty))?;
            sep = ", ";
        }
        write!(f, ") -> {}", pr(fn_sig.output()))
    }
}

impl Display for Pr<ClosureKind> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let clsr_kind = self.unpr;
        match clsr_kind {
            ClosureKind::Fn => write!(f, ""),
            ClosureKind::FnMut => write!(f, "mut"),
            ClosureKind::FnOnce => write!(f, "once"),
        }
    }
}

pub fn pr_adt_name(adt_def: &AdtDef) -> String {
    if adt_def.is_box() {
        "Box".to_string()
    } else {
        let name = pr_name(adt_def.did);
        if "std::fmt::".is_prefix_of(&name) {
            "<fmt>".to_string()
        } else {
            name
        }
    }
}

impl Display for Pr<Ty<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult { self.unpr.ty.fmt(f) }
}
impl Display for Pr<rustc_middle::ty::Ty<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let ty = self.unpr;
        match &ty.kind() {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Char => write!(f, "char"),
            TyKind::Int(_) | TyKind::Uint(_) => write!(f, "int"),
            TyKind::Float(_) => write!(f, "float"),
            TyKind::Adt(adt_def, generic_args) => {
                write!(f, "{}{}", pr_adt_name(adt_def), pr(generic_args))
            }
            TyKind::Str => write!(f, "str"),
            TyKind::Array(ty, cnst) => write!(f, "[{}; {}]", pr(ty), pr(cnst)),
            TyKind::Foreign(_) => write!(f, "<foreign>"),
            TyKind::Slice(ty) => write!(f, "[{}]", pr(ty)),
            TyKind::RawPtr(_) => write!(f, "<raw_ptr>"),
            TyKind::Ref(_, ty, Mutability::Not) => write!(f, "&{}", pr(ty)),
            TyKind::Ref(_, ty, Mutability::Mut) => write!(f, "&mut {}", pr(ty)),
            TyKind::FnDef(fun, generic_args) => with_tcx(|tcx| {
                let fn_sig = tcx.fn_sig(*fun).skip_binder();
                write!(f, "fn {}{}{}", pr_fun_name(*fun), pr(generic_args), pr(fn_sig))
            }),
            TyKind::FnPtr(poly_fn_sig) => {
                write!(f, "fn {}", pr(poly_fn_sig.skip_binder()))
            }
            TyKind::Closure(fun, generic_args) => {
                let len = generic_args.len();
                let from = with_tcx(|tcx| tcx.generics_of(*fun).parent_count);
                let clsr_kind = generic_args.type_at(from).to_opt_closure_kind().unwrap();
                write!(f, "{}{{", pr(clsr_kind))?;
                let mut sep = "";
                for i in from + 2..len {
                    write!(f, "{}{}", sep, pr(generic_args.type_at(i)))?;
                    sep = ", ";
                }
                write!(f, "}}({})", pr_name(*fun))
            }
            TyKind::Dynamic(_, _) => write!(f, "<dyn>"),
            TyKind::Never => write!(f, "!"),
            TyKind::Tuple(generic_args) => {
                write!(f, "(")?;
                let mut sep = "";
                let mut cnt = 0;
                for ty in generic_args.types() {
                    write!(f, "{}{}", sep, pr(ty))?;
                    sep = ", ";
                    cnt += 1;
                }
                write!(f, "{})", if cnt == 1 { "," } else { "" })
            }
            TyKind::Projection(_) => write!(f, "<proj>"),
            TyKind::Opaque(_, _) => write!(f, "<opaque>"),
            TyKind::Param(param_ty) => write!(f, "{}", param_ty.name),
            _ => panic!("unsupported type {}", ty),
        }
    }
}

impl Display for Pr<Local> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let local = self.unpr;
        write!(f, "_{}", local.index())
    }
}
impl Display for Pr<VariantIdx> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let variant_index = self.unpr;
        write!(f, "${}", variant_index.index())
    }
}
impl Display for Pr<FieldIdx> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let fld = self.unpr;
        write!(f, "{}", fld.index())
    }
}
impl Display for Pr<&Place<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let Place { local, projection } = self.unpr;
        write!(f, "{}", pr(local))?;
        for proj in projection.iter() {
            match proj {
                ProjectionElem::Deref => write!(f, ".*")?,
                ProjectionElem::Field(field_index, _) => write!(f, ".{}", pr(field_index))?,
                ProjectionElem::Index(local) => write!(f, "[{}]", pr(local))?,
                ProjectionElem::ConstantIndex { offset, from_end, .. } => {
                    let sign = if from_end { "-" } else { "" };
                    write!(f, "[{}{}]", sign, offset)?;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    write!(f, "[{}:-{}{}]", from, to, if from_end { " rev" } else { "" })?;
                }
                ProjectionElem::Downcast(_, variant_index) => write!(f, "<{}>", pr(variant_index))?,
            }
        }
        Ok(())
    }
}

impl Display for Pr<&GenericArgs<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let generic_args = self.unpr;
        let mut sep = "<";
        for ty in generic_args.types() {
            write!(f, "{}{}", sep, pr(ty))?;
            sep = ", ";
        }
        if sep != "<" {
            write!(f, ">")?;
        }
        Ok(())
    }
}

impl<'tcx> Display for Pr<&TyConst<'tcx>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let cnst = self.unpr;
        if let TyKind::FnDef(fun, generic_args) = cnst.ty.kind() {
            write!(f, "{}{}", pr_fun_name(*fun), pr(generic_args))
        } else {
            let buf = format!("{}", cnst);
            match cnst.ty.kind() {
                TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                    write!(f, "{}", buf.split('_').next().unwrap())
                }
                _ => write!(f, "{}", buf),
            }
        }
    }
}

fn pr_bits<'tcx>(ty: Ty<'tcx>, bits: u128, tcx: TyCtxt<'tcx>) -> impl Display + 'tcx {
    pr(TyConst::from_bits(tcx, bits, ParamEnv::reveal_all().and(ty.ty)))
}

impl Display for Pr<&Operand<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let opd = self.unpr;
        match opd {
            Operand::Copy(place) => write!(f, "{}", pr(place)),
            Operand::Move(place) => write!(f, "<-{}", pr(place)),
            Operand::Constant(box constant) => {
                write!(f, "{}", pr(constant.literal.const_for_ty().unwrap()))
            }
        }
    }
}

impl Display for Pr<BorrowKind> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let bor_kind = self.unpr;
        match bor_kind {
            BorrowKind::Shared => write!(f, "&"),
            BorrowKind::Mut { .. } => write!(f, "&mut "),
            _ => panic!("unsupported borrow kind {:?}", bor_kind),
        }
    }
}
impl Display for Pr<MirBinOp> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let bin_op = self.unpr;
        match bin_op {
            MirBinOp::Add => write!(f, "+"),
            MirBinOp::Sub => write!(f, "-"),
            MirBinOp::Mul => write!(f, "*"),
            MirBinOp::Div => write!(f, "/"),
            MirBinOp::Rem => write!(f, "%"),
            MirBinOp::BitXor => write!(f, "^"),
            MirBinOp::BitAnd => write!(f, "&"),
            MirBinOp::BitOr => write!(f, "|"),
            MirBinOp::Shl => write!(f, "<<"),
            MirBinOp::Shr => write!(f, ">>"),
            MirBinOp::Eq => write!(f, "=="),
            MirBinOp::Lt => write!(f, "<"),
            MirBinOp::Le => write!(f, "<="),
            MirBinOp::Ne => write!(f, "!="),
            MirBinOp::Ge => write!(f, ">="),
            MirBinOp::Gt => write!(f, ">"),
            MirBinOp::Offset => panic!("unsupported binary operator {:?}", bin_op),
        }
    }
}
impl Display for Pr<NullOp> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        match self.unpr {
            NullOp::SizeOf => write!(f, "sizeof"),
            NullOp::AlignOf => write!(f, "alignof"),
        }
    }
}
impl Display for Pr<MirUnOp> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        match self.unpr {
            MirUnOp::Not => write!(f, "!"),
            MirUnOp::Neg => write!(f, "-"),
        }
    }
}
impl Display for Pr<&Rvalue<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let rvalue = self.unpr;
        match rvalue {
            Rvalue::Use(opd) => write!(f, "{}", pr(opd)),
            Rvalue::Repeat(opd, n) => write!(f, "[{};{}]", pr(opd), n),
            Rvalue::Ref(_, bor_kind, place) => write!(f, "{}{}", pr(bor_kind), pr(place)),
            Rvalue::Len(place) => write!(f, "{}.len", pr(place)),
            Rvalue::Cast(_, opd, ty) => write!(f, "{} as {}", pr(opd), pr(ty)),
            Rvalue::BinaryOp(bin_op, box (opd1, opd2)) => {
                write!(f, "{} {} {}", pr(opd1), pr(bin_op), pr(opd2))
            }
            Rvalue::NullaryOp(null_op, ty) => write!(f, "{}<{}>", pr(null_op), pr(ty)),
            Rvalue::UnaryOp(un_op, opd) => write!(f, "{}{}", pr(un_op), pr(opd)),
            Rvalue::Discriminant(place) => write!(f, "{}.tag", pr(place)),
            Rvalue::Aggregate(box AggregateKind::Array(_), opds) => {
                write!(f, "[")?;
                let mut sep = "";
                for opd in opds.iter() {
                    write!(f, "{}{}", sep, pr(opd))?;
                    sep = ", ";
                }
                write!(f, "]")
            }
            _ => panic!("unsupported rvalue {:?}", rvalue),
        }
    }
}

impl Display for Pr<&Statement<'_>> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let stmt = self.unpr;
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                write!(f, "{} := {}", pr(place), pr(rvalue))
            }
            StatementKind::SetDiscriminant { place: box place, variant_index } => {
                write!(f, "{}.tag := {}", pr(place), variant_index.index())
            }
            StatementKind::StorageLive(local) => write!(f, "live {}", pr(local)),
            StatementKind::StorageDead(local) => write!(f, "dead {}", pr(local)),
            StatementKind::AscribeUserType(_, _) => write!(f, "ascribe type"),
            StatementKind::Nop => write!(f, "nop"),
            _ => panic!("unsupported statement {:?}", stmt),
        }
    }
}

struct PrTerminatorShort<'tcx> {
    terminator: &'tcx Terminator<'tcx>,
    mir: &'tcx MirBody<'tcx>,
    tcx: TyCtxt<'tcx>,
}
fn pr_terminator_short<'tcx>(
    terminator: &'tcx Terminator<'tcx>,
    mir: &'tcx MirBody<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
    PrTerminatorShort { terminator, mir, tcx }
}
impl Display for PrTerminatorShort<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let PrTerminatorShort { terminator, mir, tcx } = *self;
        match &terminator.kind {
            TerminatorKind::Goto { .. } => Ok(()),
            TerminatorKind::SwitchInt { discr, .. } => write!(f, "? {}", pr(discr)),
            TerminatorKind::Unreachable => write!(f, "panic"),
            TerminatorKind::Return => write!(f, "return _0"),
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(mir, tcx).ty;
                write!(f, "drop<{}>({})", pr(ty), pr(place))
            }
            TerminatorKind::Call { func, args, destination, .. } => {
                if let Some((place, _)) = destination {
                    write!(f, "{} := ", pr(place))?;
                }
                write!(f, "{}(", pr(func))?;
                let mut sep = "";
                for arg in args {
                    write!(f, "{}{}", sep, pr(arg))?;
                    sep = ", ";
                }
                write!(f, ")")
            }
            TerminatorKind::Assert { cond, expected, .. } => {
                write!(f, "assert!({} == {})", pr(cond), expected)
            }
            _ => panic!("unsupported terminator {:?}", terminator),
        }
    }
}
struct PrTerminator<'tcx> {
    terminator: &'tcx Terminator<'tcx>,
    mir: &'tcx MirBody<'tcx>,
    tcx: TyCtxt<'tcx>,
}
fn pr_terminator<'tcx>(
    terminator: &'tcx Terminator<'tcx>,
    mir: &'tcx MirBody<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
    PrTerminator { terminator, mir, tcx }
}
impl Display for PrTerminator<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let PrTerminator { terminator, mir, tcx } = *self;
        write!(f, "{}", pr_terminator_short(terminator, mir, tcx))?;
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                write!(f, "goto {}", pr(target))?;
            }
            TerminatorKind::SwitchInt { switch_ty, targets, .. } => {
                write!(f, " [")?;
                for (val, tgt) in targets.iter() {
                    let label = pr_bits(Ty::new(switch_ty), val, tcx).to_string();
                    write!(f, "{} -> goto {}, ", label, pr(tgt))?;
                }
                write!(f, "else -> goto {}]", pr(targets.otherwise()))?;
            }
            TerminatorKind::Unreachable | TerminatorKind::Return => {}
            TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                write!(f, "; goto {}", pr(target))?;
            }
            TerminatorKind::Call { destination, .. } => {
                if let Some((_, target)) = destination {
                    write!(f, "; goto {}", pr(target))?;
                }
            }
            _ => {
                panic!("unsupported terminator {:?}", terminator);
            }
        }
        Ok(())
    }
}

impl Display for Pr<BasicBlock> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let bb = self.unpr;
        write!(f, "bb{}", bb.index())
    }
}

struct PrSig<'tcx> {
    mir: &'tcx MirBody<'tcx>,
    fun: DefId,
}
fn pr_sig<'tcx>(mir: &'tcx MirBody<'tcx>, fun: DefId) -> impl Display + 'tcx { PrSig { mir, fun } }
impl Display for PrSig<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let PrSig { mir, fun } = *self;
        write!(f, "fn {}", pr_name(fun))?;
        with_tcx(|tcx| match &tcx.type_of(fun).kind() {
            TyKind::FnDef(_, generic_args) => write!(f, "{}", pr(generic_args)),
            TyKind::Closure(_, _) => Ok(()),
            _ => panic!("unknown function type"),
        })?;
        write!(f, "(")?;
        let mut sep = "";
        for arg in mir.args_iter() {
            let ty = &mir.local_decls[arg].ty;
            write!(f, "{}{}: {}", sep, pr(arg), pr(ty))?;
            sep = ", ";
        }
        write!(f, ") → _0: {}", pr(mir.return_ty()))
    }
}

struct PrVar<'tcx> {
    local: Local,
    local_decl: &'tcx LocalDecl<'tcx>,
}
fn pr_var<'tcx>(local: Local, local_decl: &'tcx LocalDecl<'tcx>) -> impl Display + 'tcx {
    PrVar { local, local_decl }
}
impl Display for PrVar<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let PrVar { local, local_decl } = *self;
        write!(f, "{}: {}", pr(local), pr(local_decl.ty))
    }
}

struct PrMir<'tcx> {
    mir: &'tcx MirBody<'tcx>,
    fun: DefId,
    tcx: TyCtxt<'tcx>,
}
pub fn pr_mir<'tcx>(
    mir: &'tcx MirBody<'tcx>,
    fun: DefId,
    tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
    PrMir { mir, fun, tcx }
}
impl Display for PrMir<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let PrMir { mir, fun, tcx } = *self;
        // signature
        writeln!(f, "{} {{ \n", pr_sig(mir, fun))?;
        // variables
        for (local, local_decl) in mir.local_decls.iter_enumerated() {
            writeln!(f, "  {}", pr_var(local, local_decl))?;
        }
        writeln!(f)?;
        // visit basic blocks
        for (bb, bbd) in enumerate_bbds(mir.basic_blocks()) {
            writeln!(f, "  [{}]", pr(bb))?;
            for stmt in &bbd.statements {
                writeln!(f, "  {}", pr(stmt))?;
            }
            writeln!(f, "  {}\n", pr_terminator(get_terminator(bbd), mir, tcx))?;
        }
        writeln!(f, "}}")
    }
}

fn html_esc<T: Display>(x: T) -> String {
    x.to_string().replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

struct PrMirDot<'tcx> {
    mir: &'tcx MirBody<'tcx>,
    fun: DefId,
    tcx: TyCtxt<'tcx>,
}
pub fn pr_mir_dot<'tcx>(
    mir: &'tcx MirBody<'tcx>,
    fun: DefId,
    tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
    PrMirDot { mir, fun, tcx }
}
impl Display for PrMirDot<'_> {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        let mir = self.mir;
        let fun = self.fun;
        let tcx = self.tcx;
        // preamble and signature
        writeln!(
            f,
            r#"digraph Body {{

  graph [ fontname = "Helvetica" ];
  node [ fontname = "Helvetica" ];
  edge [ fontname = "Helvetica" ];

  label = <<table border="0">"
    <tr><td align="left">{}</td></tr>"#,
            html_esc(pr_sig(mir, fun))
        )?;
        // variables
        for (local, local_decl) in mir.local_decls.iter_enumerated() {
            writeln!(
                f,
                r#"    <tr><td align="left">{}</td></tr>"#,
                html_esc(pr_var(local, local_decl))
            )?;
        }
        write!(f, "  </table>>;\n\n")?;
        let mut jumps = Vec::<(BasicBlock, BasicBlock, String)>::new();
        // visit basic blocks
        for (bb, bbd) in enumerate_bbds(mir.basic_blocks()) {
            writeln!(
                f,
                r##"  {} [
    shape = "box",
    label = <<table border="0">
      <tr><td align="center" bgcolor="#88f6fc">{}</td></tr>"##,
                pr(bb),
                pr(bb)
            )?;
            for stmt in &bbd.statements {
                writeln!(f, r#"      <tr><td align="left">{}</td></tr>"#, html_esc(pr(stmt)))?;
            }
            let terminator = get_terminator(bbd);
            match &terminator.kind {
                TerminatorKind::Goto { .. } => {}
                TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Unreachable
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Return
                | TerminatorKind::Call { .. }
                | TerminatorKind::Drop { .. } => {
                    let bgcolor = if let TerminatorKind::SwitchInt { .. } = &terminator.kind {
                        "#f8ccff"
                    } else {
                        "#d1ffeb"
                    };
                    writeln!(
                        f,
                        r#"      <tr><td align="left" bgcolor="{}">{}</td></tr>"#,
                        bgcolor,
                        html_esc(pr_terminator_short(terminator, mir, tcx))
                    )?;
                }
                _ => panic!("unsupported terminator {:?}", terminator),
            }
            match &terminator.kind {
                TerminatorKind::Goto { target }
                | TerminatorKind::Drop { target, .. }
                | TerminatorKind::Assert { target, .. } => {
                    jumps.push((bb, *target, String::new()));
                }
                TerminatorKind::SwitchInt { switch_ty, targets, .. } => {
                    for (val, tgt) in targets.iter() {
                        let label = pr_bits(Ty::new(switch_ty), val, tcx).to_string();
                        jumps.push((bb, tgt, label));
                    }
                    jumps.push((bb, targets.otherwise(), "else".to_string()));
                }
                TerminatorKind::Unreachable | TerminatorKind::Return => {}
                TerminatorKind::Call { destination, .. } => {
                    if let Some((_, target)) = destination {
                        jumps.push((bb, *target, String::new()));
                    }
                }
                _ => panic!("unsupported terminator {:?}", terminator),
            }
            writeln!(f, "    </table>>\n  ];\n")?;
        }
        // jumps and postlude
        for (bb, bb2, label) in &jumps {
            write!(f, "  {} -> {}", pr(bb), pr(bb2))?;
            if !label.is_empty() {
                write!(f, r##" [taillabel = "{}", fontcolor = "#ef8cff"]"##, label)?;
            }
            writeln!(f, ";")?;
        }
        writeln!(f, "\n}}")
    }
}
