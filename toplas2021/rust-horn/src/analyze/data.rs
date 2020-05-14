use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use rustc_middle::mir::{
  BasicBlock as BB, BinOp as MirBinOp, Body, BorrowKind as BorK, Field as FldIdx, Local, NullOp,
  Operand, Place, ProjectionElem as ProjElem, Rvalue, UnOp as MirUnOp,
};
use rustc_middle::ty::subst::{InternalSubsts as Substs, Subst};
use rustc_middle::ty::{Const as TyConst, FieldDef, Ty, TyCtxt, TyKind as TyK};
use rustc_target::abi::VariantIdx as VrtIdx;

use std::collections::{HashMap as Map, HashSet as Set};
use std::mem::swap;

use crate::prettify::{pr, pr_fun_name};
use crate::represent::{rep, rep_drop_name};
use crate::util::{only_ty, sort_map, FLD0, FLD1, VRT0};

#[derive(Copy, Clone)]
pub struct Outer<'tcx> {
  pub mir: &'tcx Body<'tcx>,
  pub substs: &'tcx Substs<'tcx>,
  pub tcx: TyCtxt<'tcx>,
}
impl<'tcx> Outer<'tcx> {
  pub fn get_bool(self) -> Ty<'tcx> { self.tcx.mk_bool() }
  pub fn local_to_ty(self, local: Local) -> Ty<'tcx> {
    let Outer { mir, substs, tcx } = self;
    mir.local_decls[local].ty.subst(tcx, substs)
  }
  pub fn local_to_expr(self, local: Local) -> Expr<'tcx> {
    Expr::Path(Path::Var(Var::Input(local), self.local_to_ty(local)))
  }
  pub fn place_to_ty(self, place: &Place<'tcx>) -> Ty<'tcx> {
    let Outer { mir, substs, tcx } = self;
    place.ty(mir, tcx).ty.subst(tcx, substs)
  }
  pub fn base_i_place_to_ty(self, place: &Place<'tcx>, i: usize) -> Ty<'tcx> {
    let Outer { mir, substs, tcx } = self;
    Place::ty_from(place.local, &place.projection[0..i], mir, tcx).ty.subst(tcx, substs)
  }
  pub fn opd_to_ty(self, opd: &Operand<'tcx>) -> Ty<'tcx> {
    let Outer { mir, substs, tcx } = self;
    opd.ty(mir, tcx).subst(tcx, substs)
  }
  pub fn rvalue_to_ty(self, rvalue: &Rvalue<'tcx>) -> Ty<'tcx> {
    let Outer { mir, substs, tcx } = self;
    rvalue.ty(mir, tcx).subst(tcx, substs)
  }
  pub fn fld_def_to_ty(self, fld_def: &FieldDef, adt_substs: &'tcx Substs<'tcx>) -> Ty<'tcx> {
    let Outer { substs, tcx, .. } = self;
    fld_def.ty(tcx, adt_substs).subst(tcx, substs)
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Var {
  Input(Local),
  SelfResult,
  SelfPanic,
  CallResult(BB),
  Rand(BB),
  MutRet(BB, usize),
  Split(BB, VrtIdx, FldIdx),
  Nonce(Option<usize>),
}

#[derive(Debug, Clone)]
pub enum Path<'tcx> {
  Var(Var, Ty<'tcx>),
  Proj(Ty<'tcx>, VrtIdx, FldIdx, Box<Path<'tcx>>),
}
pub fn get_proj<'tcx>(
  ty: Ty<'tcx>, vrt_idx: VrtIdx, fld_idx: FldIdx, path: Path<'tcx>,
) -> Path<'tcx> {
  match path {
    Path::Var(Var::Nonce(None), _) => path,
    Path::Var(Var::Nonce(Some(_)), _) => panic!("named nonce cannot be projected"),
    _ => Path::Proj(ty, vrt_idx, fld_idx, box path),
  }
}

#[derive(Debug, Copy, Clone)]
pub enum Const {
  Bool(bool),
  Int(i64),
  Real(f64),
  Unit,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
  Add,
  Sub,
  Mul,
  DivInt,
  Mod,
  DivReal,
  And,
  Eq,
  Lt,
  Le,
  Ne,
  Ge,
  Gt,
}
fn mir_bin_op_to_bin_op(mir_bin_op: MirBinOp, ty: Ty) -> BinOp {
  match mir_bin_op {
    MirBinOp::Add => BinOp::Add,
    MirBinOp::Sub => BinOp::Sub,
    MirBinOp::Mul => BinOp::Mul,
    MirBinOp::Div => match &ty.kind {
      TyK::Int(_) | TyK::Uint(_) => BinOp::DivInt,
      TyK::Float(_) => BinOp::DivReal,
      _ => panic!("unexpected type {} for division", ty),
    },
    MirBinOp::Rem => BinOp::Mod,
    MirBinOp::BitAnd => BinOp::And,
    MirBinOp::Eq => BinOp::Eq,
    MirBinOp::Lt => BinOp::Lt,
    MirBinOp::Le => BinOp::Le,
    MirBinOp::Ne => BinOp::Ne,
    MirBinOp::Ge => BinOp::Ge,
    MirBinOp::Gt => BinOp::Gt,
    _ => panic!("unsupported binary operator {:?}", mir_bin_op),
  }
}
pub fn fun_to_bin_op(fun: DefId) -> Option<BinOp> {
  let fun_name = pr_fun_name(fun);
  if fun_name == "<eq>" {
    Some(BinOp::Eq)
  } else if fun_name == "<ne>" {
    Some(BinOp::Ne)
  } else if fun_name == "<add>" {
    Some(BinOp::Add)
  } else if fun_name == "<div-int>" {
    Some(BinOp::DivInt)
  } else {
    None
  }
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
  Neg,
  Not,
  Abs,
}
pub fn mir_un_op_to_un_op(mir_un_op: MirUnOp) -> UnOp {
  match mir_un_op {
    MirUnOp::Not => UnOp::Not,
    MirUnOp::Neg => UnOp::Neg,
  }
}
pub fn fun_to_un_op(fun: DefId) -> Option<UnOp> {
  let fun_name = pr_fun_name(fun);
  if fun_name == "<abs>" {
    Some(UnOp::Abs)
  } else {
    None
  }
}

#[derive(Debug, Clone)]
pub enum Expr<'tcx> {
  Path(Path<'tcx>),
  Const(Const),
  BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
  UnOp(UnOp, Box<Expr<'tcx>>),
  Aggr(Ty<'tcx>, VrtIdx, Vec<Expr<'tcx>>),
}
pub fn var_to_expr<'tcx>(var: Var, ty: Ty<'tcx>) -> Expr<'tcx> { Expr::Path(Path::Var(var, ty)) }
pub fn nonce<'tcx>(ty: Ty<'tcx>) -> Expr<'tcx> { var_to_expr(Var::Nonce(None), ty) }

pub fn path_ty<'tcx>(path: &Path<'tcx>) -> Ty<'tcx> {
  match path {
    Path::Var(_, ty) => ty,
    Path::Proj(ty, _, _, _) => ty,
  }
}
pub fn ty_body<'tcx>(ty: Ty<'tcx>) -> Ty<'tcx> {
  match &ty.kind {
    TyK::Ref(_, ty, Mutability::Not) => ty_body(ty),
    TyK::Adt(adt_def, adt_substs) if adt_def.is_box() => ty_body(only_ty(adt_substs)),
    _ => ty,
  }
}

pub fn decompose_mut<'tcx>(mx: Expr<'tcx>) -> (Expr<'tcx>, Expr<'tcx>) {
  match mx {
    Expr::Path(path) => {
      let ty = ty_body(path_ty(&path));
      match &ty.kind {
        TyK::Ref(_, _, Mutability::Mut) => {}
        _ => panic!("unexpected type {:?} for a mutable reference", ty),
      }
      (
        Expr::Path(Path::Proj(ty, VRT0, FLD0, box path.clone())),
        Expr::Path(Path::Proj(ty, VRT0, FLD1, box path.clone())),
      )
    }
    Expr::Aggr(_, VRT0, mut xx_) if xx_.len() == 2 => {
      let x_ = xx_.pop().unwrap();
      let x = xx_.pop().unwrap();
      (x, x_)
    }
    _ => panic!("unexpected expression {:?} for a mutable reference", mx),
  }
}

pub fn bin_op_expr<'tcx>(bin_op: BinOp, expr1: Expr<'tcx>, expr2: Expr<'tcx>) -> Expr<'tcx> {
  match bin_op {
    BinOp::Ne => Expr::UnOp(UnOp::Not, box Expr::BinOp(BinOp::Eq, box expr1, box expr2)),
    _ => Expr::BinOp(bin_op, box expr1, box expr2),
  }
}

pub fn is_fun_swap(fun: DefId) -> bool { pr_fun_name(fun) == "<swap>" }
pub fn is_fun_vacuous(fun: DefId) -> bool { pr_fun_name(fun) == "<free>" }

pub type Env<'tcx> = Map<Local, Expr<'tcx>>;

#[derive(Debug, Copy, Clone)]
struct Proj<'tcx> {
  base_ty: Ty<'tcx>,
  vrt_idx: VrtIdx,
  fld_idx: FldIdx,
}
#[derive(Debug)]
struct Site<'tcx> {
  local: Local,
  projs: Vec<Proj<'tcx>>,
}

fn place_to_site<'tcx>(place: &Place<'tcx>, outer: Outer<'tcx>) -> Site<'tcx> {
  let Place { local, projection } = place;
  let mut projs = Vec::<Proj>::new();
  let mut vrt_idx = VRT0;
  for (i, proj) in projection.iter().enumerate() {
    let mut next_vrt_idx = VRT0;
    let base_ty = outer.base_i_place_to_ty(place, i);
    match &proj {
      ProjElem::Deref => match &base_ty.kind {
        TyK::Ref(_, _, Mutability::Not) => {}
        TyK::Adt(adt_def, _) if adt_def.is_box() => {}
        TyK::Ref(_, _, Mutability::Mut) => {
          projs.push(Proj { vrt_idx: VRT0, fld_idx: FLD0, base_ty })
        }
        _ => panic!("unexpected type {} for dereference", base_ty),
      },
      ProjElem::Downcast(_, vrt_idx) => {
        next_vrt_idx = *vrt_idx;
      }
      ProjElem::Field(fld_idx, _) => {
        match &base_ty.kind {
          TyK::Adt(adt_def, _) => assert!(
            vrt_idx.index() < adt_def.variants.len()
              && fld_idx.index() < adt_def.variants[vrt_idx].fields.len()
          ),
          TyK::Tuple(substs) => {
            assert!(vrt_idx == VRT0 && fld_idx.index() < substs.types().count())
          }
          _ => panic!("unexpected type {} for taking a field", base_ty),
        };
        projs.push(Proj { vrt_idx, fld_idx: *fld_idx, base_ty });
      }
      _ => panic!("unsupported projection element {:?}", proj),
    }
    vrt_idx = next_vrt_idx;
  }
  return Site { local: *local, projs };
}

pub fn read_place<'tcx>(place: &Place<'tcx>, env: &Env<'tcx>, outer: Outer<'tcx>) -> Expr<'tcx> {
  let Site { local, projs } = place_to_site(place, outer);
  let mut expr = match env.get(&local) {
    None => nonce(outer.place_to_ty(place)),
    Some(expr) => expr.clone(),
  };
  for &proj in projs.iter() {
    let Proj { base_ty, vrt_idx, fld_idx } = proj;
    expr = match expr {
      Expr::Path(path) => Expr::Path(get_proj(base_ty, vrt_idx, fld_idx, path)),
      Expr::Aggr(_, vrt_idx2, mut flds) => {
        assert!(vrt_idx == vrt_idx2);
        flds.remove(fld_idx.index())
      }
      _ => panic!("unexpected expr {:?}", &expr),
    }
  }
  expr
}

fn get_n_flds(base_ty: Ty, vrt_idx: VrtIdx) -> usize {
  match &base_ty.kind {
    TyK::Ref(_, _, Mutability::Mut) => 2,
    TyK::Adt(adt_def, _) => {
      assert!(!adt_def.is_box());
      assert!(vrt_idx.index() < adt_def.variants.len());
      adt_def.variants[vrt_idx].fields.len()
    }
    TyK::Tuple(substs) => substs.types().count(),
    _ => panic!("unexpected type {} for projection", base_ty),
  }
}

pub fn seize_place<'a, 'tcx>(
  place: &Place<'tcx>, env: &'a mut Env<'tcx>, outer: Outer<'tcx>,
) -> &'a mut Expr<'tcx> {
  let Site { local, projs } = place_to_site(place, outer);
  let mut expr = env.entry(local).or_insert(nonce(outer.place_to_ty(place)));
  for &elem in projs.iter() {
    let Proj { base_ty, vrt_idx, fld_idx } = elem;
    expr = match expr {
      Expr::Path(path) => {
        *expr = Expr::Aggr(
          base_ty,
          vrt_idx,
          (0..get_n_flds(base_ty, vrt_idx))
            .map(|i| Expr::Path(get_proj(base_ty, vrt_idx, FldIdx::from(i), path.clone())))
            .collect(),
        );
        if let Expr::Aggr(_, _, flds) = expr {
          &mut flds[fld_idx.index()]
        } else {
          unreachable!()
        }
      }
      Expr::Aggr(_, vrt_idx2, flds) => {
        assert!(vrt_idx == *vrt_idx2);
        &mut flds[fld_idx.index()]
      }
      _ => panic!("unexpected expr {:?}", expr),
    }
  }
  expr
}

fn ty_cnst_to_cnst<'tcx>(ty_cnst: &'tcx TyConst<'tcx>) -> Const {
  let buf = pr(ty_cnst).to_string();
  match &ty_cnst.ty.kind {
    TyK::Int(_) | TyK::Uint(_) => Const::Int(buf.parse().unwrap()),
    TyK::Float(_) => Const::Real(buf.parse().unwrap()),
    TyK::Bool => Const::Bool(buf.parse().unwrap()),
    TyK::Tuple(substs) if substs.len() == 0 => Const::Unit,
    _ => panic!("unexpected type {:?}", ty_cnst.ty),
  }
}

pub fn read_opd<'tcx>(opd: &Operand<'tcx>, env: &mut Env<'tcx>, outer: Outer<'tcx>) -> Expr<'tcx> {
  match opd {
    Operand::Copy(place) => read_place(place, env, outer),
    Operand::Move(place) => {
      let expr = seize_place(place, env, outer);
      let mut res = nonce(outer.place_to_ty(place));
      swap(expr, &mut res);
      res
    }
    Operand::Constant(box constant) => Expr::Const(ty_cnst_to_cnst(constant.literal)),
  }
}

pub fn read_rvalue<'tcx>(
  rvalue: &Rvalue<'tcx>, env: &mut Env<'tcx>, outer: Outer<'tcx>, me: BB, i: usize,
) -> Expr<'tcx> {
  let ty = outer.rvalue_to_ty(rvalue);
  match rvalue {
    Rvalue::Use(opd) => read_opd(opd, env, outer),
    Rvalue::Ref(_, BorK::Shared, place) => read_place(place, env, outer),
    Rvalue::Ref(_, BorK::Mut { .. }, place) => {
      let expr = seize_place(place, env, outer);
      let var = Var::MutRet(me, i);
      let ty2 = outer.place_to_ty(place);
      let mut expr_buf = var_to_expr(var, ty2);
      swap(expr, &mut expr_buf);
      Expr::Aggr(ty, VRT0, vec![expr_buf, var_to_expr(var, ty2)])
    }
    Rvalue::BinaryOp(mir_bin_op, opd1, opd2) => {
      let bin_op = mir_bin_op_to_bin_op(*mir_bin_op, outer.opd_to_ty(opd1));
      bin_op_expr(bin_op, read_opd(opd1, env, outer), read_opd(opd2, env, outer))
    }
    Rvalue::NullaryOp(NullOp::Box, _) => nonce(ty),
    Rvalue::UnaryOp(mir_un_op, opd) => {
      Expr::UnOp(mir_un_op_to_un_op(*mir_un_op), box read_opd(opd, env, outer))
    }
    _ => panic!("unexpected rvalue {:?}", rvalue),
  }
}

pub fn set_tag<'tcx>(place: &Place<'tcx>, tag: VrtIdx, env: &mut Env<'tcx>, outer: Outer<'tcx>) {
  let expr = seize_place(place, env, outer);
  let base_ty = outer.place_to_ty(place);
  match expr {
    Expr::Path(path) => {
      let n_flds = get_n_flds(base_ty, tag);
      *expr = Expr::Aggr(
        base_ty,
        tag,
        (0..n_flds)
          .map(|i| Expr::Path(get_proj(base_ty, tag, FldIdx::from(i), path.clone())))
          .collect(),
      );
    }
    Expr::Aggr(_, vrt_idx, _) => assert!(tag == *vrt_idx),
    _ => panic!("unexpected expr {:?}", expr),
  }
}

fn needs_drop<'tcx>(ty: Ty<'tcx>, outer: Outer<'tcx>, seen: &mut Set<String>) -> bool {
  match &ty.kind {
    TyK::Bool | TyK::Int(_) | TyK::Uint(_) | TyK::Float(_) => false,
    TyK::Adt(adt_def, adt_substs) => {
      if adt_def.is_box() {
        needs_drop(only_ty(*adt_substs), outer, seen)
      } else {
        let key = rep(ty).to_string();
        if !seen.contains(&key) {
          seen.insert(key);
          adt_def
            .all_fields()
            .any(|fld_def| needs_drop(outer.fld_def_to_ty(fld_def, adt_substs), outer, seen))
        } else {
          false
        }
      }
    }
    TyK::Ref(_, _, Mutability::Not) => false,
    TyK::Ref(_, _, Mutability::Mut) => true,
    TyK::Tuple(substs) => substs.types().any(|ty| needs_drop(ty, outer, seen)),
    _ => panic!("unsupported type {}", ty),
  }
}
fn drop_path<'tcx>(ty: Ty<'tcx>, path: &Path<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
  if let Path::Var(Var::Nonce(_), _) = path {
    return;
  }
  match &ty.kind {
    TyK::Ref(_, _, Mutability::Mut) => {
      conds.push(Cond::Eq {
        src: Expr::Path(get_proj(ty, VRT0, FLD0, path.clone())),
        tgt: Expr::Path(get_proj(ty, VRT0, FLD1, path.clone())),
      });
    }
    TyK::Adt(adt_def, adt_substs) => {
      if adt_def.is_box() {
        drop_path(only_ty(*adt_substs), path, conds);
      } else {
        conds.push(Cond::Drop { ty, arg: Expr::Path(path.clone()) });
      }
    }
    _ => panic!("unexpected type {}", ty),
  }
}
pub fn drop_expr<'tcx>(
  ty: Ty<'tcx>, arg: &Expr<'tcx>, conds: &mut Vec<Cond<'tcx>>, outer: Outer<'tcx>,
) {
  match &arg {
    Expr::Path(path) => {
      if needs_drop(ty, outer, &mut Set::new()) {
        drop_path(ty, path, conds);
      }
    }
    Expr::Aggr(ty, vrt_idx, flds) => match &ty.kind {
      TyK::Ref(_, _, Mutability::Mut) => {
        let (x, x_) = decompose_mut(arg.clone());
        conds.push(Cond::Eq { tgt: x_, src: x });
      }
      TyK::Adt(adt_def, adt_substs) => {
        assert!(!adt_def.is_box());
        assert!(vrt_idx.index() < adt_def.variants.len());
        let fld_defs = &adt_def.variants[*vrt_idx].fields;
        assert!(flds.len() == fld_defs.len());
        for (fld_def, fld) in fld_defs.iter().zip(flds.iter()) {
          drop_expr(outer.fld_def_to_ty(fld_def, adt_substs), fld, conds, outer);
        }
      }
      TyK::Tuple(substs) => {
        assert!(flds.len() == substs.types().count());
        for (ty, fld) in substs.types().zip(flds.iter()) {
          drop_expr(ty, fld, conds, outer);
        }
      }
      _ => panic!("unexpected type {} for aggregation", ty),
    },
    _ => {}
  }
}

pub fn assign_to_place<'tcx>(
  place: &Place<'tcx>, mut new_expr: Expr<'tcx>, env: &mut Env<'tcx>, conds: &mut Vec<Cond<'tcx>>,
  outer: Outer<'tcx>,
)
{
  let expr = seize_place(place, env, outer);
  swap(expr, &mut new_expr);
  drop_expr(outer.place_to_ty(place), &new_expr, conds, outer);
}

#[derive(Debug)]
pub enum Cond<'tcx> {
  Drop { ty: Ty<'tcx>, arg: Expr<'tcx> },
  Eq { tgt: Expr<'tcx>, src: Expr<'tcx> },
  Call { fun_ty: Ty<'tcx>, args: Vec<Expr<'tcx>> },
}
#[derive(Debug)]
pub enum End<'tcx> {
  Pivot { pivot: BB, args: Vec<Expr<'tcx>> },
  Return { res: Option<Expr<'tcx>> },
  Panic,
  NeverReturn,
}

fn traverse_path<'tcx>(path: &mut Path<'tcx>, vars: &mut Map<Var, Ty<'tcx>>, n_nonces: &mut usize) {
  match path {
    Path::Var(var, ty) => {
      if let Var::Nonce(i) = var {
        assert!(i.is_none());
        *i = Some(*n_nonces);
        *n_nonces += 1;
      }
      vars.insert(*var, ty);
    }
    Path::Proj(_, _, _, box path) => traverse_path(path, vars, n_nonces),
  }
}
fn traverse_expr<'tcx>(expr: &mut Expr<'tcx>, vars: &mut Map<Var, Ty<'tcx>>, n_nonces: &mut usize) {
  match expr {
    Expr::Path(path) => traverse_path(path, vars, n_nonces),
    Expr::Const(_) => {}
    Expr::BinOp(_, box expr1, box expr2) => {
      traverse_expr(expr1, vars, n_nonces);
      traverse_expr(expr2, vars, n_nonces);
    }
    Expr::UnOp(_, box expr) => traverse_expr(expr, vars, n_nonces),
    Expr::Aggr(_, _, flds) => {
      for fld in flds.iter_mut() {
        traverse_expr(fld, vars, n_nonces);
      }
    }
  }
}
fn traverse_cond<'tcx>(
  cond: &mut Cond<'tcx>, drop_asks: &mut Map<String, Ty<'tcx>>, vars: &mut Map<Var, Ty<'tcx>>,
  n_nonces: &mut usize,
)
{
  match cond {
    Cond::Drop { ty, arg } => {
      traverse_expr(arg, vars, n_nonces);
      drop_asks.insert(rep_drop_name(*ty), *ty);
    }
    Cond::Eq { tgt, src } => {
      traverse_expr(tgt, vars, n_nonces);
      traverse_expr(src, vars, n_nonces);
    }
    Cond::Call { args, .. } => {
      for arg in args.iter_mut() {
        traverse_expr(arg, vars, n_nonces);
      }
    }
  }
}
fn traverse_end<'tcx>(end: &mut End<'tcx>, vars: &mut Map<Var, Ty<'tcx>>, n_nonces: &mut usize) {
  match end {
    End::Pivot { args, .. } => {
      for arg in args.iter_mut() {
        traverse_expr(arg, vars, n_nonces);
      }
    }
    End::Return { res } => match res {
      Some(expr) => traverse_expr(expr, vars, n_nonces),
      None => {}
    },
    End::Panic | End::NeverReturn => {}
  }
}
fn traverse_ty<'tcx>(
  ty: Ty<'tcx>, outer: Outer<'tcx>, adt_asks: &mut Set<DefId>,
  tup_asks: &mut Map<String, &'tcx Substs<'tcx>>, mut_asks: &mut Map<String, Ty<'tcx>>,
)
{
  match &ty.kind {
    TyK::Bool | TyK::Int(_) | TyK::Uint(_) | TyK::Float(_) => {}
    TyK::Adt(adt_def, adt_substs) => {
      if adt_def.is_box() {
        for ty in adt_substs.types() {
          traverse_ty(ty, outer, adt_asks, tup_asks, mut_asks);
        }
      } else if !adt_asks.contains(&adt_def.did) {
        adt_asks.insert(adt_def.did);
        for fld_def in adt_def.all_fields() {
          traverse_ty(
            outer.fld_def_to_ty(fld_def, adt_substs),
            outer,
            adt_asks,
            tup_asks,
            mut_asks,
          );
        }
      }
    }
    TyK::Ref(_, ty, mutimmut) => {
      if let Mutability::Mut = mutimmut {
        mut_asks.insert(rep(ty).to_string(), ty);
      }
      traverse_ty(ty, outer, adt_asks, tup_asks, mut_asks);
    }
    TyK::Tuple(substs) => {
      tup_asks.insert(rep(substs).to_string(), substs);
      for ty in substs.types() {
        traverse_ty(ty, outer, adt_asks, tup_asks, mut_asks)
      }
    }
    _ => panic!("unsupported type {}", ty),
  }
}

#[derive(Debug)]
pub struct BasicAsks<'tcx> {
  pub fun_asks: Map<String, Ty<'tcx>>,
  pub drop_asks: Map<String, Ty<'tcx>>,
  pub adt_asks: Set<DefId>,
  pub tup_asks: Map<String, &'tcx Substs<'tcx>>,
  pub mut_asks: Map<String, Ty<'tcx>>,
}

pub fn traverse_prerule<'tcx>(
  args: &mut Vec<Expr<'tcx>>, conds: &mut Vec<Cond<'tcx>>, end: &mut End<'tcx>, outer: Outer<'tcx>,
  basic_asks: &mut BasicAsks<'tcx>,
) -> Vec<(Var, Ty<'tcx>)>
{
  let BasicAsks { drop_asks, adt_asks, tup_asks, mut_asks, .. } = basic_asks;
  let mut vars: Map<Var, Ty> = Map::new();
  let mut n_nonces = 0;
  for arg in args.iter_mut() {
    traverse_expr(arg, &mut vars, &mut n_nonces);
  }
  for cond in conds.iter_mut() {
    traverse_cond(cond, drop_asks, &mut vars, &mut n_nonces);
  }
  traverse_end(end, &mut vars, &mut n_nonces);
  for (_, ty) in vars.iter() {
    traverse_ty(ty, outer, adt_asks, tup_asks, mut_asks);
  }
  sort_map(vars)
}
