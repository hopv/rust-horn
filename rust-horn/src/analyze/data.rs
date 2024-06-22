use std::mem::swap;

use crate::prettify::{pr, pr_fun_name};
use crate::represent::{rep, rep_drop_name};
use crate::types::{
  adt_is_box, BasicBlock, BorrowKind, DefId, FieldDef, FieldIdx, GenericArgs, GenericArgsRef,
  Local, Map, MirBinOp, MirBody, MirUnOp, Mutability, Operand, Place, ProjectionElem, Rvalue, Set,
  Subst, Ty, TyConst, TyCtxt, TyKind, VariantIdx,
};
use crate::util::{FLD0, FLD1, VRT0};

#[derive(Copy, Clone)]
pub struct MirAccess<'tcx> {
  pub mir: &'tcx MirBody<'tcx>,
  pub generic_args: GenericArgsRef<'tcx>,
  pub tcx: TyCtxt<'tcx>,
}
impl<'tcx> MirAccess<'tcx> {
  pub fn get_bool(self) -> Ty<'tcx> { Ty::new(self.tcx.mk_ty(TyKind::Bool)) }
}

pub trait MirAccessExt<'tcx> {
  fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx>;
}

impl<'tcx> MirAccessExt<'tcx> for Local {
  fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
    let local = *self;
    let MirAccess { mir, generic_args, tcx } = mir_access;
    Ty::new(mir.local_decls[local].ty.subst(tcx, generic_args))
  }
}

impl<'tcx> MirAccessExt<'tcx> for Place<'tcx> {
  fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
    let MirAccess { mir, generic_args, tcx } = mir_access;
    Ty::new(self.ty(mir, tcx).ty.subst(tcx, generic_args))
  }
}

impl<'tcx> MirAccessExt<'tcx> for Operand<'tcx> {
  fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
    let MirAccess { mir, generic_args, tcx } = mir_access;
    Ty::new(self.ty(mir, tcx).subst(tcx, generic_args))
  }
}

impl<'tcx> MirAccessExt<'tcx> for Rvalue<'tcx> {
  fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
    let MirAccess { mir, generic_args, tcx } = mir_access;
    Ty::new(self.ty(mir, tcx).subst(tcx, generic_args))
  }
}

pub trait MirAccessCtxExt<'tcx> {
  type Context;
  fn get_ty_with(&self, mir_access: MirAccess<'tcx>, context: Self::Context) -> Ty<'tcx>;
}

impl<'tcx> MirAccessCtxExt<'tcx> for Place<'tcx> {
  type Context = usize;

  fn get_ty_with(&self, mir_access: MirAccess<'tcx>, i: Self::Context) -> Ty<'tcx> {
    let MirAccess { mir, generic_args, tcx } = mir_access;
    Ty::new(
      Place::ty_from(self.local, &self.projection[0..i], mir, tcx).ty.subst(tcx, generic_args),
    )
  }
}

impl<'tcx> MirAccessCtxExt<'tcx> for FieldDef {
  type Context = GenericArgsRef<'tcx>;

  fn get_ty_with(&self, mir_access: MirAccess<'tcx>, adt_substs: Self::Context) -> Ty<'tcx> {
    let MirAccess { generic_args, tcx, .. } = mir_access;
    Ty::new(self.ty(tcx, adt_substs).subst(tcx, generic_args))
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Var {
  Input(Local),
  SelfResult,
  SelfPanic,
  CallResult(BasicBlock),
  Rand(BasicBlock),
  MutRet(BasicBlock, usize),
  Split(BasicBlock, VariantIdx, FieldIdx),
  /// Uninitialized value
  Nonce,
}

#[derive(Debug, Clone)]
pub enum Path<'tcx> {
  Var(Var, Ty<'tcx>),
  Proj(Ty<'tcx>, VariantIdx, FieldIdx, Box<Path<'tcx>>),
}

impl<'tcx> Path<'tcx> {
  fn ty(&self) -> Ty<'tcx> {
    match self {
      Path::Var(_, ty) => *ty,
      Path::Proj(ty, _, _, _) => *ty,
    }
  }
  pub fn get_proj(&self, ty: Ty<'tcx>, variant_index: VariantIdx, field_index: FieldIdx) -> Self {
    match self {
      Path::Var(Var::Nonce, _) => self.clone(),
      _ => Path::Proj(ty, variant_index, field_index, Box::new(self.clone())),
    }
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

impl BinOp {
  fn from_mir_bin_op(mir_bin_op: MirBinOp, ty: Ty) -> Self {
    match mir_bin_op {
      MirBinOp::Add => BinOp::Add,
      MirBinOp::Sub => BinOp::Sub,
      MirBinOp::Mul => BinOp::Mul,
      MirBinOp::Div => match &ty.kind() {
        TyKind::Int(_) | TyKind::Uint(_) => BinOp::DivInt,
        TyKind::Float(_) => BinOp::DivReal,
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

  pub fn try_from_fun(fun: DefId) -> Option<Self> {
    match pr_fun_name(fun).as_str() {
      "<eq>" => Some(BinOp::Eq),
      "<ne>" => Some(BinOp::Ne),
      "<add>" => Some(BinOp::Add),
      "<div-int>" => Some(BinOp::DivInt),
      _ => None,
    }
  }
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
  Neg,
  Not,
  Abs,
}
impl UnOp {
  pub fn from_mir_un_op(mir_un_op: MirUnOp) -> Self {
    match mir_un_op {
      MirUnOp::Not => Self::Not,
      MirUnOp::Neg => Self::Neg,
    }
  }
  pub fn try_from_fun(fun: DefId) -> Option<UnOp> {
    match pr_fun_name(fun).as_str() {
      "<abs>" => Some(UnOp::Abs),
      _ => None,
    }
  }
}

#[derive(Debug, Clone)]
pub enum Expr<'tcx> {
  Path(Path<'tcx>),
  Const(Const),
  BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
  UnOp(UnOp, Box<Expr<'tcx>>),
  Aggregate(Ty<'tcx>, VariantIdx, Vec<Expr<'tcx>>),
}

impl<'tcx> Expr<'tcx> {
  pub fn from_var(var: Var, ty: Ty<'tcx>) -> Self { Expr::Path(Path::Var(var, ty)) }
  pub fn nonce(ty: Ty<'tcx>) -> Self { Self::from_var(Var::Nonce, ty) }

  pub fn from_bin_op(bin_op: BinOp, expr1: Self, expr2: Self) -> Self {
    match bin_op {
      BinOp::Ne => {
        Expr::UnOp(UnOp::Not, Box::new(Expr::BinOp(BinOp::Eq, Box::new(expr1), Box::new(expr2))))
      }
      _ => Expr::BinOp(bin_op, Box::new(expr1), Box::new(expr2)),
    }
  }
}

impl Ty<'_> {
  pub fn ty_body(&self) -> Self {
    match self.kind() {
      TyKind::Ref(_, ty, Mutability::Not) => return Ty::new(ty).ty_body(),
      TyKind::Adt(adt_def, adt_substs) => {
        if let Some(ty) = adt_is_box(adt_def, adt_substs) {
          return ty.ty_body();
        }
      }
      _ => (),
    };
    *self
  }
}

impl Expr<'_> {
  pub fn decompose_mut(self) -> (Self, Self) {
    match self {
      Expr::Path(path) => {
        let ty = path.ty().ty_body();
        match &ty.kind() {
          TyKind::Ref(_, _, Mutability::Mut) => {}
          _ => panic!("unexpected type {:?} for a mutable reference", ty),
        }
        (
          Expr::Path(Path::Proj(ty, VRT0, FLD0, Box::new(path.clone()))),
          Expr::Path(Path::Proj(ty, VRT0, FLD1, Box::new(path.clone()))),
        )
      }
      Expr::Aggregate(_, VRT0, mut xx_) if xx_.len() == 2 => {
        let x_ = xx_.pop().unwrap();
        let x = xx_.pop().unwrap();
        (x, x_)
      }
      _ => panic!("unexpected expression {:?} for a mutable reference", self),
    }
  }
}

pub type Env<'tcx> = Map<Local, Expr<'tcx>>;

#[derive(Debug, Copy, Clone)]
struct Proj<'tcx> {
  base_ty: Ty<'tcx>,
  variant_index: VariantIdx,
  field_index: FieldIdx,
}
#[derive(Debug)]
struct Site<'tcx> {
  local: Local,
  projs: Vec<Proj<'tcx>>,
}

impl<'tcx> Site<'tcx> {
  fn from_place(place: &Place<'tcx>, mir_access: MirAccess<'tcx>) -> Self {
    let Place { local, projection } = place;
    let mut projs = Vec::<Proj>::new();
    let mut variant_index = VRT0;
    for (i, proj) in projection.iter().enumerate() {
      let mut next_variant_index = VRT0;
      let base_ty = place.get_ty_with(mir_access, i);
      match &proj {
        ProjectionElem::Deref => match &base_ty.kind() {
          TyKind::Ref(_, _, Mutability::Not) => {}
          TyKind::Adt(adt_def, _) if adt_def.is_box() => {}
          TyKind::Ref(_, _, Mutability::Mut) => {
            projs.push(Proj { variant_index: VRT0, field_index: FLD0, base_ty })
          }
          _ => panic!("unexpected type {} for dereference", base_ty),
        },
        ProjectionElem::Downcast(_, variant_index) => {
          next_variant_index = *variant_index;
        }
        ProjectionElem::Field(field_index, _) => {
          match &base_ty.kind() {
            TyKind::Adt(adt_def, _) => assert!(
              variant_index.index() < adt_def.variants.len()
                && field_index.index() < adt_def.variants[variant_index].fields.len()
            ),
            TyKind::Tuple(generic_args) => {
              assert!(variant_index == VRT0 && field_index.index() < generic_args.types().count())
            }
            _ => panic!("unexpected type {} for taking a field", base_ty),
          };
          projs.push(Proj { variant_index, field_index: *field_index, base_ty });
        }
        _ => panic!("unsupported projection element {:?}", proj),
      }
      variant_index = next_variant_index;
    }
    Site { local: *local, projs }
  }
}

pub fn read_place<'tcx>(
  place: &Place<'tcx>, env: &Env<'tcx>, mir_access: MirAccess<'tcx>,
) -> Expr<'tcx> {
  let Site { local, projs } = Site::from_place(place, mir_access);
  let mut expr = match env.get(&local) {
    None => Expr::nonce(place.get_ty(mir_access)),
    Some(expr) => expr.clone(),
  };
  for &proj in projs.iter() {
    let Proj { base_ty, variant_index, field_index } = proj;
    expr = match expr {
      Expr::Path(path) => Expr::Path(path.get_proj(base_ty, variant_index, field_index)),
      Expr::Aggregate(_, variant_index2, mut flds) => {
        assert!(variant_index == variant_index2);
        flds.remove(field_index.index())
      }
      _ => panic!("unexpected expr {:?}", &expr),
    }
  }
  expr
}

fn get_n_flds(base_ty: Ty, variant_index: VariantIdx) -> usize {
  match &base_ty.kind() {
    TyKind::Ref(_, _, Mutability::Mut) => 2,
    TyKind::Adt(adt_def, _) => {
      assert!(!adt_def.is_box());
      assert!(variant_index.index() < adt_def.variants.len());
      adt_def.variants[variant_index].fields.len()
    }
    TyKind::Tuple(generic_args) => generic_args.types().count(),
    _ => panic!("unexpected type {} for projection", base_ty),
  }
}

pub fn seize_place<'a, 'tcx>(
  place: &Place<'tcx>, env: &'a mut Env<'tcx>, mir_access: MirAccess<'tcx>,
) -> &'a mut Expr<'tcx> {
  let Site { local, projs } = Site::from_place(place, mir_access);
  let mut expr = env.entry(local).or_insert_with(|| Expr::nonce(place.get_ty(mir_access)));
  for &elem in projs.iter() {
    let Proj { base_ty, variant_index, field_index } = elem;
    expr = match expr {
      Expr::Path(path) => {
        *expr = Expr::Aggregate(
          base_ty,
          variant_index,
          (0..get_n_flds(base_ty, variant_index))
            .map(|i| Expr::Path(path.get_proj(base_ty, variant_index, FieldIdx::from(i))))
            .collect(),
        );
        if let Expr::Aggregate(_, _, flds) = expr {
          &mut flds[field_index.index()]
        } else {
          unreachable!()
        }
      }
      Expr::Aggregate(_, variant_index2, flds) => {
        assert!(variant_index == *variant_index2);
        &mut flds[field_index.index()]
      }
      _ => panic!("unexpected expr {:?}", expr),
    }
  }
  expr
}

fn ty_cnst_to_cnst(ty_cnst: &TyConst<'_>) -> Const {
  let buf = pr(ty_cnst).to_string();
  match &ty_cnst.ty.kind() {
    TyKind::Int(_) | TyKind::Uint(_) => Const::Int(buf.parse().unwrap()),
    TyKind::Float(_) => Const::Real(buf.parse().unwrap()),
    TyKind::Bool => Const::Bool(buf.parse().unwrap()),
    TyKind::Tuple(generic_args) if generic_args.len() == 0 => Const::Unit,
    _ => panic!("unexpected type {:?}", ty_cnst.ty),
  }
}

pub fn read_opd<'tcx>(
  opd: &Operand<'tcx>, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>,
) -> Expr<'tcx> {
  match opd {
    Operand::Copy(place) => read_place(place, env, mir_access),
    Operand::Move(place) => {
      let expr = seize_place(place, env, mir_access);
      let mut res = Expr::nonce(place.get_ty(mir_access));
      swap(expr, &mut res);
      res
    }
    Operand::Constant(box constant) => {
      Expr::Const(ty_cnst_to_cnst(constant.literal.const_for_ty().unwrap()))
    }
  }
}

pub fn read_rvalue<'tcx>(
  rvalue: &Rvalue<'tcx>, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>, me: BasicBlock,
  stmt_index: usize,
) -> Expr<'tcx> {
  let ty = rvalue.get_ty(mir_access);
  match rvalue {
    Rvalue::Use(opd) => read_opd(opd, env, mir_access),
    Rvalue::Ref(_, BorrowKind::Shared, place) => read_place(place, env, mir_access),
    Rvalue::Ref(_, BorrowKind::Mut { .. }, place) => {
      let expr = seize_place(place, env, mir_access);
      let var = Var::MutRet(me, stmt_index);
      let ty2 = place.get_ty(mir_access);
      let mut expr_buf = Expr::from_var(var, ty2);
      swap(expr, &mut expr_buf);
      Expr::Aggregate(ty, VRT0, vec![expr_buf, Expr::from_var(var, ty2)])
    }
    Rvalue::BinaryOp(mir_bin_op, box (opd1, opd2)) => {
      let bin_op = BinOp::from_mir_bin_op(*mir_bin_op, opd1.get_ty(mir_access));
      Expr::from_bin_op(bin_op, read_opd(opd1, env, mir_access), read_opd(opd2, env, mir_access))
    }
    Rvalue::UnaryOp(mir_un_op, opd) => {
      Expr::UnOp(UnOp::from_mir_un_op(*mir_un_op), Box::new(read_opd(opd, env, mir_access)))
    }
    _ => panic!("unexpected rvalue {:?}", rvalue),
  }
}

pub fn set_tag<'tcx>(
  place: &Place<'tcx>, tag: VariantIdx, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>,
) {
  let expr = seize_place(place, env, mir_access);
  let base_ty = place.get_ty(mir_access);
  match expr {
    Expr::Path(path) => {
      let n_flds = get_n_flds(base_ty, tag);
      *expr = Expr::Aggregate(
        base_ty,
        tag,
        (0..n_flds).map(|i| Expr::Path(path.get_proj(base_ty, tag, FieldIdx::from(i)))).collect(),
      );
    }
    Expr::Aggregate(_, variant_index, _) => assert!(tag == *variant_index),
    _ => panic!("unexpected expr {:?}", expr),
  }
}

fn needs_drop<'tcx>(ty: Ty<'tcx>, mir_access: MirAccess<'tcx>, seen: &mut Set<String>) -> bool {
  match &ty.kind() {
    TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => false,
    TyKind::Adt(adt_def, adt_substs) => {
      if let Some(ty) = adt_is_box(adt_def, adt_substs) {
        needs_drop(ty, mir_access, seen)
      } else {
        let key = rep(ty).to_string();
        if seen.insert(key) {
          adt_def.all_fields().any(|fld_def| {
            needs_drop(fld_def.get_ty_with(mir_access, adt_substs), mir_access, seen)
          })
        } else {
          false
        }
      }
    }
    TyKind::Ref(_, _, Mutability::Not) => false,
    TyKind::Ref(_, _, Mutability::Mut) => true,
    TyKind::Tuple(generic_args) => {
      generic_args.types().any(|ty| needs_drop(Ty::new(ty), mir_access, seen))
    }
    _ => panic!("unsupported type {}", ty),
  }
}
fn drop_path<'tcx>(ty: Ty<'tcx>, path: &Path<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
  if let Path::Var(Var::Nonce, _) = path {
    return;
  }
  match &ty.kind() {
    TyKind::Ref(_, _, Mutability::Mut) => {
      conds.push(Cond::Eq {
        src: Expr::Path(path.get_proj(ty, VRT0, FLD0)),
        tgt: Expr::Path(path.get_proj(ty, VRT0, FLD1)),
      });
    }
    TyKind::Adt(adt_def, adt_substs) => {
      if let Some(ty) = adt_is_box(adt_def, adt_substs) {
        drop_path(ty, path, conds);
      } else {
        conds.push(Cond::Drop { ty, arg: Expr::Path(path.clone()) });
      }
    }
    _ => panic!("unexpected type {}", ty),
  }
}
pub fn drop_expr<'tcx>(
  ty: Ty<'tcx>, arg: &Expr<'tcx>, conds: &mut Vec<Cond<'tcx>>, mir_access: MirAccess<'tcx>,
) {
  match &arg {
    Expr::Path(path) => {
      if needs_drop(ty, mir_access, &mut Set::new()) {
        drop_path(ty, path, conds);
      }
    }
    Expr::Aggregate(ty, variant_index, flds) => match &ty.kind() {
      TyKind::Ref(_, _, Mutability::Mut) => {
        let (x, x_) = arg.clone().decompose_mut();
        conds.push(Cond::Eq { tgt: x_, src: x });
      }
      TyKind::Adt(adt_def, adt_substs) => {
        assert!(!adt_def.is_box());
        assert!(variant_index.index() < adt_def.variants.len());
        let fld_defs = &adt_def.variants[*variant_index].fields;
        assert!(flds.len() == fld_defs.len());
        for (fld_def, fld) in fld_defs.iter().zip(flds.iter()) {
          drop_expr(fld_def.get_ty_with(mir_access, adt_substs), fld, conds, mir_access);
        }
      }
      TyKind::Tuple(generic_args) => {
        assert!(flds.len() == generic_args.types().count());
        for (ty, fld) in generic_args.types().zip(flds.iter()) {
          drop_expr(Ty::new(ty), fld, conds, mir_access);
        }
      }
      _ => panic!("unexpected type {} for aggregation", ty),
    },
    _ => {}
  }
}

pub fn assign_to_place<'tcx>(
  place: &Place<'tcx>, mut new_expr: Expr<'tcx>, env: &mut Env<'tcx>, conds: &mut Vec<Cond<'tcx>>,
  mir_access: MirAccess<'tcx>,
) {
  let expr = seize_place(place, env, mir_access);
  swap(expr, &mut new_expr);
  drop_expr(place.get_ty(mir_access), &new_expr, conds, mir_access);
}

#[derive(Debug)]
pub enum Cond<'tcx> {
  Drop { ty: Ty<'tcx>, arg: Expr<'tcx> },
  Eq { tgt: Expr<'tcx>, src: Expr<'tcx> },
  Neq { tgt: Expr<'tcx>, srcs: Vec<Expr<'tcx>> },
  Call { fun_ty: Ty<'tcx>, args: Vec<Expr<'tcx>> },
}
#[derive(Debug)]
pub enum End<'tcx> {
  Pivot { next_switch: BasicBlock, args: Vec<Expr<'tcx>> },
  Return { res: Option<Expr<'tcx>> },
  Panic,
  NeverReturn,
}

fn traverse_path<'tcx>(path: &mut Path<'tcx>, vars: &mut Map<Var, Ty<'tcx>>) {
  match path {
    Path::Var(var, ty) => {
      vars.insert(*var, *ty);
    }
    Path::Proj(_, _, _, box path) => traverse_path(path, vars),
  }
}
fn traverse_expr<'tcx>(expr: &mut Expr<'tcx>, vars: &mut Map<Var, Ty<'tcx>>) {
  match expr {
    Expr::Path(path) => traverse_path(path, vars),
    Expr::Const(_) => {}
    Expr::BinOp(_, box expr1, box expr2) => {
      traverse_expr(expr1, vars);
      traverse_expr(expr2, vars);
    }
    Expr::UnOp(_, box expr) => traverse_expr(expr, vars),
    Expr::Aggregate(_, _, flds) => {
      for fld in flds.iter_mut() {
        traverse_expr(fld, vars);
      }
    }
  }
}
fn traverse_cond<'tcx>(
  cond: &mut Cond<'tcx>, drop_asks: &mut Map<String, Ty<'tcx>>, vars: &mut Map<Var, Ty<'tcx>>,
) {
  match cond {
    Cond::Drop { ty, arg } => {
      traverse_expr(arg, vars);
      drop_asks.insert(rep_drop_name(*ty), *ty);
    }
    Cond::Eq { tgt, src } => {
      traverse_expr(tgt, vars);
      traverse_expr(src, vars);
    }
    Cond::Neq { tgt, srcs } => {
      traverse_expr(tgt, vars);
      for src in srcs.iter_mut() {
        traverse_expr(src, vars);
      }
    }
    Cond::Call { args, .. } => {
      for arg in args.iter_mut() {
        traverse_expr(arg, vars);
      }
    }
  }
}
fn traverse_end<'tcx>(end: &mut End<'tcx>, vars: &mut Map<Var, Ty<'tcx>>) {
  match end {
    End::Pivot { args, .. } => {
      for arg in args.iter_mut() {
        traverse_expr(arg, vars);
      }
    }
    End::Return { res } => match res {
      Some(expr) => traverse_expr(expr, vars),
      None => {}
    },
    End::Panic | End::NeverReturn => {}
  }
}
fn traverse_ty<'tcx>(
  ty: Ty<'tcx>, mir_access: MirAccess<'tcx>, adt_asks: &mut Set<DefId>,
  tup_asks: &mut Map<String, &'tcx GenericArgs<'tcx>>, mut_asks: &mut Map<String, Ty<'tcx>>,
) {
  match &ty.kind() {
    TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {}
    TyKind::Adt(adt_def, adt_substs) => {
      if adt_def.is_box() {
        for ty in adt_substs.types() {
          traverse_ty(Ty::new(ty), mir_access, adt_asks, tup_asks, mut_asks);
        }
      } else if adt_asks.insert(adt_def.did) {
        for fld_def in adt_def.all_fields() {
          traverse_ty(
            fld_def.get_ty_with(mir_access, adt_substs),
            mir_access,
            adt_asks,
            tup_asks,
            mut_asks,
          );
        }
      }
    }
    TyKind::Ref(_, ty, mutability) => {
      let ty = Ty::new(ty);
      if let Mutability::Mut = mutability {
        mut_asks.insert(rep(ty).to_string(), ty);
      }
      traverse_ty(ty, mir_access, adt_asks, tup_asks, mut_asks);
    }
    TyKind::Tuple(generic_args) => {
      tup_asks.insert(rep(generic_args).to_string(), generic_args);
      for ty in generic_args.types() {
        let ty = Ty::new(ty);
        traverse_ty(ty, mir_access, adt_asks, tup_asks, mut_asks)
      }
    }
    _ => panic!("unsupported type {}", ty),
  }
}

#[derive(Debug)]
/// Ask is a request to define at the beginning of the smt2 to be generated.
pub struct BasicAsks<'tcx> {
  pub fun_asks: Map<String, Ty<'tcx>>,
  pub drop_asks: Map<String, Ty<'tcx>>,
  pub adt_asks: Set<DefId>,
  pub tup_asks: Map<String, GenericArgsRef<'tcx>>,
  pub mut_asks: Map<String, Ty<'tcx>>,
}

pub fn traverse_prerule<'tcx>(
  args: &mut Vec<Expr<'tcx>>, conds: &mut Vec<Cond<'tcx>>, end: &mut End<'tcx>,
  mir_access: MirAccess<'tcx>, basic_asks: &mut BasicAsks<'tcx>,
) -> Vec<(Var, Ty<'tcx>)> {
  let BasicAsks { drop_asks, adt_asks, tup_asks, mut_asks, .. } = basic_asks;
  let mut vars: Map<Var, Ty> = Map::new();
  for arg in args.iter_mut() {
    traverse_expr(arg, &mut vars);
  }
  for cond in conds.iter_mut() {
    traverse_cond(cond, drop_asks, &mut vars);
  }
  traverse_end(end, &mut vars);
  let vars = vars.into_inner_vec();
  for (_, ty) in &vars {
    traverse_ty(*ty, mir_access, adt_asks, tup_asks, mut_asks);
  }
  vars
}
