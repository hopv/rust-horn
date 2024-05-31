pub use rustc_hir::{def_id::DefId, Mutability};
pub use rustc_index::vec::IndexVec;
pub use rustc_middle::mir::{
  interpret::{ConstValue, Scalar},
  AggregateKind, BasicBlock, BasicBlockData, BinOp as MirBinOp, Body as MirBody, BorrowKind,
  Field as FieldIdx, Local, LocalDecl, NullOp, Operand, Place, ProjectionElem, Rvalue, Statement,
  StatementKind, Terminator, TerminatorKind, UnOp as MirUnOp,
};
pub use rustc_middle::ty::{
  subst::{InternalSubsts as GenericArgs, Subst, SubstsRef as GenericArgsRef},
  tls::with as with_tcx,
  AdtDef, ClosureKind, Const as TyConst, ConstKind, FieldDef, FnSig, ParamEnv, TyCtxt, TyKind,
  VariantDef,
};
pub use rustc_session::config::EntryFnType;
pub type BasicBlockDatas<'tcx> = IndexVec<BasicBlock, BasicBlockData<'tcx>>;
pub use rustc_target::abi::VariantIdx;

pub use std::collections::{HashMap as Map, HashSet as Set};
use std::fmt::Display;

#[derive(Debug, Copy, Clone)]
pub struct Ty<'tcx> {
  pub ty: rustc_middle::ty::Ty<'tcx>,
}

impl<'tcx> Display for Ty<'tcx> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.ty.fmt(f) }
}

impl<'tcx> Ty<'tcx> {
  pub fn new(ty: rustc_middle::ty::Ty<'tcx>) -> Self { Self { ty } }
}

impl<'tcx> std::ops::Deref for Ty<'tcx> {
  type Target = rustc_middle::ty::Ty<'tcx>;

  fn deref(&self) -> &Self::Target { &self.ty }
}
