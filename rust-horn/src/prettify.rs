use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use rustc_middle::mir::{
  AggregateKind as AggrK, BasicBlock as BB, BinOp, Body, BorrowKind as BorK, Field, Local,
  LocalDecl, NullOp, Operand, Place, ProjectionElem as ProjElem, Rvalue, Statement as Stmt,
  StatementKind as StmtK, Terminator as Tmnt, TerminatorKind as TmntK, UnOp,
};
use rustc_middle::ty::subst::InternalSubsts as Substs;
use rustc_middle::ty::tls::with as with_tcx;
use rustc_middle::ty::{AdtDef, ClosureKind, Const, FnSig, Ty, TyCtxt, TyKind as TyK};
use rustc_target::abi::VariantIdx as VrtIdx;

use std::fmt::{Display, Formatter, Result as FResult};
use std::iter::once;
use std::str::pattern::Pattern;

use crate::util::{bits_to_cnst, enumerate_bbds, get_tmnt, Cap};

pub fn pr_name(def_id: DefId) -> String {
  with_tcx(|tcx| tcx.def_path_str(def_id)).replace("{{closure}}", "{clsr}")
}

pub fn pr_fun_name(fun: DefId) -> String {
  let name = pr_name(fun);
  if name == "rand" {
    format!("<rand>")
  } else if name == "alloc::alloc::box_free" {
    format!("<free>")
  } else if name == "std::io::_print" {
    format!("<print>")
  } else if name == "std::cmp::PartialEq::eq" {
    format!("<eq>")
  } else if name == "std::cmp::PartialEq::ne" {
    format!("<ne>")
  } else if name == "std::ops::Add::add" {
    format!("<add>")
  } else if name == "std::mem::swap" {
    format!("<swap>")
  } else if "core::num::<impl".is_prefix_of(&name) && ">::abs".is_suffix_of(&name) {
    format!("<abs>")
  } else if name == "std::rt::begin_panic" {
    format!("<panic>")
  } else if name == "std::intrinsics::discriminant_value" {
    format!("<tag>")
  } else if name == "std::ops::Fn::call" {
    format!("<call>")
  } else if "std::fmt".is_prefix_of(&name) {
    format!("<fmt>")
  } else {
    name
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

impl Display for Pr<&FnSig<'_>> {
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
    format!("Box")
  } else {
    let name = pr_name(adt_def.did);
    if "std::fmt::".is_prefix_of(&name) {
      format!("<fmt>")
    } else {
      name
    }
  }
}

impl Display for Pr<Ty<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let ty = self.unpr;
    match &ty.kind {
      TyK::Bool => write!(f, "bool"),
      TyK::Char => write!(f, "char"),
      TyK::Int(_) | TyK::Uint(_) => write!(f, "int"),
      TyK::Float(_) => write!(f, "float"),
      TyK::Adt(adt_def, substs) => write!(f, "{}{}", pr_adt_name(adt_def), pr(substs)),
      TyK::Str => write!(f, "str"),
      TyK::Array(ty, cnst) => write!(f, "[{}; {}]", pr(ty), pr(cnst)),
      TyK::Foreign(_) => write!(f, "<foreign>"),
      TyK::Slice(ty) => write!(f, "[{}]", pr(ty)),
      TyK::RawPtr(_) => write!(f, "<raw_ptr>"),
      TyK::Ref(_, ty, Mutability::Not) => write!(f, "&{}", pr(ty)),
      TyK::Ref(_, ty, Mutability::Mut) => write!(f, "&mut {}", pr(ty)),
      TyK::FnDef(fun, substs) => with_tcx(|tcx| {
        let poly_fn_sig = tcx.fn_sig(*fun);
        let fn_sig = poly_fn_sig.skip_binder();
        write!(f, "fn {}{}{}", pr_fun_name(*fun), pr(substs), pr(fn_sig))
      }),
      TyK::FnPtr(poly_fn_sig) => {
        let fn_sig = poly_fn_sig.skip_binder();
        write!(f, "fn {}", pr(fn_sig))
      }
      TyK::Closure(fun, substs) => {
        let len = substs.len();
        let from = with_tcx(|tcx| tcx.generics_of(*fun).parent_count);
        let clsr_kind = substs.type_at(from).to_opt_closure_kind().unwrap();
        write!(f, "{}{{", pr(clsr_kind))?;
        let mut sep = "";
        for i in from + 2..len {
          write!(f, "{}{}", sep, pr(substs.type_at(i)))?;
          sep = ", ";
        }
        write!(f, "}}({})", pr_name(*fun))
      }
      TyK::Dynamic(_, _) => write!(f, "<dyn>"),
      TyK::Never => write!(f, "!"),
      TyK::Tuple(substs) => {
        write!(f, "(")?;
        let mut sep = "";
        let mut cnt = 0;
        for ty in substs.types() {
          write!(f, "{}{}", sep, pr(ty))?;
          sep = ", ";
          cnt += 1;
        }
        write!(f, "{})", if cnt == 1 { "," } else { "" })
      }
      TyK::Projection(_) => write!(f, "<proj>"),
      TyK::Opaque(_, _) => write!(f, "<opaque>"),
      TyK::Param(param_ty) => write!(f, "{}", param_ty.name),
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
impl Display for Pr<VrtIdx> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let vrt_idx = self.unpr;
    write!(f, "${}", vrt_idx.index())
  }
}
impl Display for Pr<Field> {
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
        ProjElem::Deref => write!(f, ".*")?,
        ProjElem::Field(fld_idx, _) => write!(f, ".{}", pr(fld_idx))?,
        ProjElem::Index(local) => write!(f, "[{}]", pr(local))?,
        ProjElem::ConstantIndex { offset, from_end, .. } => {
          let sign = if *from_end { "-" } else { "" };
          write!(f, "[{}{}]", sign, offset)?;
        }
        ProjElem::Subslice { from, to, from_end } => {
          write!(f, "[{}:-{}{}]", from, to, if *from_end { " rev" } else { "" })?
        }
        ProjElem::Downcast(_, vrt_idx) => write!(f, "<{}>", pr(vrt_idx))?,
      }
    }
    Ok(())
  }
}

impl Display for Pr<&Substs<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let substs = self.unpr;
    let mut sep = "<";
    for ty in substs.types() {
      write!(f, "{}{}", sep, pr(ty))?;
      sep = ", ";
    }
    if sep != "<" {
      write!(f, ">")?;
    }
    Ok(())
  }
}

impl<'tcx> Display for Pr<&'tcx Const<'tcx>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let cnst = self.unpr;
    if let TyK::FnDef(fun, substs) = &cnst.ty.kind {
      write!(f, "{}{}", pr_fun_name(*fun), pr(substs))
    } else {
      let buf = format!("{}", cnst);
      match &cnst.ty.kind {
        TyK::Int(_) | TyK::Uint(_) | TyK::Float(_) => {
          let pat = |c: char| c.is_ascii_alphabetic();
          write!(f, "{}", buf.split(pat).next().unwrap())
        }
        _ => write!(f, "{}", buf),
      }
    }
  }
}

fn pr_bits<'tcx>(ty: Ty<'tcx>, bits: u128, tcx: TyCtxt<'tcx>) -> impl Display + Cap<'tcx> {
  pr(bits_to_cnst(ty, bits, tcx))
}

impl Display for Pr<&Operand<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let opd = self.unpr;
    match opd {
      Operand::Copy(place) => write!(f, "{}", pr(place)),
      Operand::Move(place) => write!(f, "<-{}", pr(place)),
      Operand::Constant(box constant) => write!(f, "{}", pr(constant.literal)),
    }
  }
}

impl Display for Pr<BorK> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let bor_kind = self.unpr;
    match bor_kind {
      BorK::Shared => write!(f, "&"),
      BorK::Mut { .. } => write!(f, "&mut "),
      _ => panic!("unsupported borrow kind {:?}", bor_kind),
    }
  }
}
impl Display for Pr<BinOp> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let bin_op = self.unpr;
    match bin_op {
      BinOp::Add => write!(f, "+"),
      BinOp::Sub => write!(f, "-"),
      BinOp::Mul => write!(f, "*"),
      BinOp::Div => write!(f, "/"),
      BinOp::Rem => write!(f, "%"),
      BinOp::BitXor => write!(f, "^"),
      BinOp::BitAnd => write!(f, "&"),
      BinOp::BitOr => write!(f, "|"),
      BinOp::Shl => write!(f, "<<"),
      BinOp::Shr => write!(f, ">>"),
      BinOp::Eq => write!(f, "=="),
      BinOp::Lt => write!(f, "<"),
      BinOp::Le => write!(f, "<="),
      BinOp::Ne => write!(f, "!="),
      BinOp::Ge => write!(f, ">="),
      BinOp::Gt => write!(f, "<"),
      _ => panic!("unsupported binary operator {:?}", bin_op),
    }
  }
}
impl Display for Pr<NullOp> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    match self.unpr {
      NullOp::SizeOf => write!(f, "sizeof"),
      NullOp::Box => write!(f, "box"),
    }
  }
}
impl Display for Pr<UnOp> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    match self.unpr {
      UnOp::Not => write!(f, "!"),
      UnOp::Neg => write!(f, "-"),
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
      Rvalue::BinaryOp(bin_op, opd1, opd2) => write!(f, "{} {} {}", pr(opd1), pr(bin_op), pr(opd2)),
      Rvalue::NullaryOp(null_op, ty) => write!(f, "{}<{}>", pr(null_op), pr(ty)),
      Rvalue::UnaryOp(un_op, opd) => write!(f, "{}{}", pr(un_op), pr(opd)),
      Rvalue::Discriminant(place) => write!(f, "{}.tag", pr(place)),
      Rvalue::Aggregate(box AggrK::Array(_), opds) => {
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

impl Display for Pr<&Stmt<'_>> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let stmt = self.unpr;
    match &stmt.kind {
      StmtK::Assign(box (place, rvalue)) => write!(f, "{} := {}", pr(place), pr(rvalue)),
      StmtK::SetDiscriminant { place: box place, variant_index } => {
        write!(f, "{}.tag := {}", pr(place), variant_index.index())
      }
      StmtK::StorageLive(local) => write!(f, "live {}", pr(local)),
      StmtK::StorageDead(local) => write!(f, "dead {}", pr(local)),
      StmtK::AscribeUserType(_, _) => write!(f, "ascribe type"),
      StmtK::Nop => write!(f, "nop"),
      _ => panic!("unsupported statement {:?}", stmt),
    }
  }
}

struct PrTmntShort<'tcx> {
  tmnt: &'tcx Tmnt<'tcx>,
  mir: &'tcx Body<'tcx>,
  tcx: TyCtxt<'tcx>,
}
fn pr_tmnt_short<'tcx>(
  tmnt: &'tcx Tmnt<'tcx>, mir: &'tcx Body<'tcx>, tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
  PrTmntShort { tmnt, mir, tcx }
}
impl Display for PrTmntShort<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let PrTmntShort { tmnt, mir, tcx } = *self;
    match &tmnt.kind {
      TmntK::Goto { .. } => Ok(()),
      TmntK::SwitchInt { discr, .. } => write!(f, "? {}", pr(discr)),
      TmntK::Unreachable => write!(f, "panic"),
      TmntK::Return => write!(f, "return _0"),
      TmntK::Drop { location, .. } => {
        let ty = location.ty(mir, tcx).ty;
        write!(f, "drop<{}>({})", pr(ty), pr(location))
      }
      TmntK::Call { func, args, destination, .. } => {
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
      TmntK::Assert { cond, expected, .. } => write!(f, "assert!({} == {})", pr(cond), expected),
      _ => panic!("unsupported terminator {:?}", tmnt),
    }
  }
}
struct PrTmnt<'tcx> {
  tmnt: &'tcx Tmnt<'tcx>,
  mir: &'tcx Body<'tcx>,
  tcx: TyCtxt<'tcx>,
}
fn pr_tmnt<'tcx>(
  tmnt: &'tcx Tmnt<'tcx>, mir: &'tcx Body<'tcx>, tcx: TyCtxt<'tcx>,
) -> impl Display + 'tcx {
  PrTmnt { tmnt, mir, tcx }
}
impl Display for PrTmnt<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let PrTmnt { tmnt, mir, tcx } = *self;
    write!(f, "{}", pr_tmnt_short(tmnt, mir, tcx))?;
    match &tmnt.kind {
      TmntK::Goto { target } => {
        write!(f, "goto {}", pr(target))?;
      }
      TmntK::SwitchInt { switch_ty, values, targets, .. } => {
        write!(f, " [")?;
        let mut sep = "";
        let labels_iter = values
          .iter()
          .map(|&bits| pr_bits(switch_ty, bits, tcx).to_string())
          .chain(once(format!("else")));
        for (label, &target) in labels_iter.zip(targets.iter()) {
          write!(f, "{}{} -> goto {}", sep, label, pr(target))?;
          sep = ", ";
        }
        write!(f, "]")?;
      }
      TmntK::Unreachable | TmntK::Return => {}
      TmntK::Drop { target, .. } | TmntK::Assert { target, .. } => {
        write!(f, "; goto {}", pr(target))?;
      }
      TmntK::Call { destination, .. } => {
        if let Some((_, target)) = destination {
          write!(f, "; goto {}", pr(target))?;
        }
      }
      _ => {
        panic!("unsupported terminator {:?}", tmnt);
      }
    }
    Ok(())
  }
}

impl Display for Pr<BB> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let bb = self.unpr;
    write!(f, "bb{}", bb.index())
  }
}

struct PrSig<'tcx> {
  mir: &'tcx Body<'tcx>,
  fun: DefId,
}
fn pr_sig<'tcx>(mir: &'tcx Body<'tcx>, fun: DefId) -> impl Display + 'tcx { PrSig { mir, fun } }
impl Display for PrSig<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let PrSig { mir, fun } = *self;
    write!(f, "fn {}", pr_name(fun))?;
    with_tcx(|tcx| match &tcx.type_of(fun).kind {
      TyK::FnDef(_, substs) => write!(f, "{}", pr(substs)),
      TyK::Closure(_, _) => Ok(()),
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
  mir: &'tcx Body<'tcx>,
  fun: DefId,
  tcx: TyCtxt<'tcx>,
}
pub fn pr_mir<'tcx>(mir: &'tcx Body<'tcx>, fun: DefId, tcx: TyCtxt<'tcx>) -> impl Display + 'tcx {
  PrMir { mir, fun, tcx }
}
impl Display for PrMir<'_> {
  fn fmt(&self, f: &mut Formatter) -> FResult {
    let PrMir { mir, fun, tcx } = *self;
    // signature
    writeln!(f, "{} {{ \n", pr_sig(mir, fun))?;
    // variables
    for (local, local_decl) in mir.local_decls.iter_enumerated() {
      writeln!(f, "  {}", pr_var(local, &local_decl))?;
    }
    writeln!(f, "")?;
    // visit basic blocks
    for (bb, bbd) in enumerate_bbds(&mir.basic_blocks()) {
      writeln!(f, "  [{}]", pr(bb))?;
      for stmt in bbd.statements.iter() {
        writeln!(f, "  {}", pr(stmt))?;
      }
      writeln!(f, "  {}\n", pr_tmnt(get_tmnt(bbd), mir, tcx))?;
    }
    writeln!(f, "}}")
  }
}

fn html_esc<T: Display>(x: T) -> String {
  x.to_string().replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
}

struct PrMirDot<'tcx> {
  mir: &'tcx Body<'tcx>,
  fun: DefId,
  tcx: TyCtxt<'tcx>,
}
pub fn pr_mir_dot<'tcx>(
  mir: &'tcx Body<'tcx>, fun: DefId, tcx: TyCtxt<'tcx>,
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
      writeln!(f, r#"    <tr><td align="left">{}</td></tr>"#, html_esc(pr_var(local, local_decl)))?;
    }
    write!(f, "  </table>>;\n\n")?;
    let mut jumps = Vec::<(BB, BB, String)>::new();
    // visit basic blocks
    for (bb, bbd) in enumerate_bbds(&mir.basic_blocks()) {
      writeln!(
        f,
        r##"  {} [
    shape = "box",
    label = <<table border="0">
      <tr><td align="center" bgcolor="#88f6fc">{}</td></tr>"##,
        pr(bb),
        pr(bb)
      )?;
      for stmt in bbd.statements.iter() {
        writeln!(f, r#"      <tr><td align="left">{}</td></tr>"#, html_esc(pr(stmt)))?;
      }
      let tmnt = get_tmnt(bbd);
      match &tmnt.kind {
        TmntK::Goto { .. } => {}
        TmntK::SwitchInt { .. }
        | TmntK::Unreachable
        | TmntK::Assert { .. }
        | TmntK::Return
        | TmntK::Call { .. }
        | TmntK::Drop { .. } => {
          let bgcolor;
          if let TmntK::SwitchInt { .. } = &tmnt.kind {
            bgcolor = "#f8ccff";
          } else {
            bgcolor = "#d1ffeb";
          }
          writeln!(
            f,
            r#"      <tr><td align="left" bgcolor="{}">{}</td></tr>"#,
            bgcolor,
            html_esc(pr_tmnt_short(tmnt, mir, tcx))
          )?;
        }
        _ => panic!("unsupported terminator {:?}", tmnt),
      }
      match &tmnt.kind {
        TmntK::Goto { target } | TmntK::Drop { target, .. } | TmntK::Assert { target, .. } => {
          jumps.push((bb, *target, format!("")));
        }
        TmntK::SwitchInt { switch_ty, values, targets, .. } => {
          let labels_iter = values
            .iter()
            .map(|&bits| pr_bits(switch_ty, bits, tcx).to_string())
            .chain(once(format!("else")));
          for (label, &target) in labels_iter.zip(targets.iter()) {
            jumps.push((bb, target, label));
          }
        }
        TmntK::Unreachable | TmntK::Return => {}
        TmntK::Call { destination, .. } => {
          if let Some((_, target)) = destination {
            jumps.push((bb, *target, format!("")));
          }
        }
        _ => panic!("unsupported terminator {:?}", tmnt),
      }
      writeln!(f, "    </table>>\n  ];\n")?;
    }
    // jumps and postlude
    for (bb, bb2, label) in jumps.iter() {
      write!(f, "  {} -> {}", pr(bb), pr(bb2))?;
      if label != "" {
        write!(f, r##" [taillabel = "{}", fontcolor = "#ef8cff"]"##, label)?;
      }
      writeln!(f, ";")?;
    }
    writeln!(f, "\n}}")
  }
}
