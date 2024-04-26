use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::{
  interpret::{ConstValue, Scalar},
  BasicBlock as BB, BasicBlockData as BBD, Body as MirBody, Field as FldIdx, Local,
  Terminator as Tmnt,
};
use rustc_middle::ty::{
  subst::InternalSubsts as Substs, Const, ConstKind, FieldDef as FldDef, ParamEnv, Ty, TyCtxt,
  TyKind as TyK,
};
use rustc_target::abi::VariantIdx as VrtIdx;
use std::cmp::Ord;
use std::collections::{HashMap as Map, HashSet as Set};

pub const BB0: BB = BB::from_u32(0);
pub const _0: Local = Local::from_u32(0);
pub const VRT0: VrtIdx = VrtIdx::from_u32(0);
pub const FLD0: FldIdx = FldIdx::from_u32(0);
pub const FLD1: FldIdx = FldIdx::from_u32(1);

pub type BBDs<'tcx> = IndexVec<BB, BBD<'tcx>>;

/* captures a lifetime */
pub trait Cap<'a> {}
impl<'a, T> Cap<'a> for T {}

pub fn enumerate_bbds<'a, 'tcx>(bbds: &'a BBDs<'tcx>) -> impl Iterator<Item = (BB, &'a BBD<'tcx>)> {
  bbds.iter().enumerate().filter(|(_, bbd)| !bbd.is_cleanup).map(|(i, bbd)| (BB::from(i), bbd))
}

pub fn enumerate_mirs<'tcx>(tcx: TyCtxt<'tcx>) -> impl Iterator<Item = (DefId, &MirBody<'tcx>)> {
  tcx
    .mir_keys(())
    .iter()
    .map(|fun| fun.to_def_id())
    .filter(move |&fun| {
      tcx.def_path(fun).data.iter().all(|elem| &elem.data.to_string() != "{{constructor}}")
    })
    .map(move |fun| {
      let mir = tcx.optimized_mir(fun);
      (fun, mir)
    })
}

pub fn enumerate_fld_defs(fld_defs: &[FldDef]) -> impl Iterator<Item = (FldIdx, &FldDef)> {
  fld_defs.iter().enumerate().map(|(i, fld_def)| (FldIdx::from(i), fld_def))
}

pub fn bits_to_cnst<'tcx>(ty: Ty<'tcx>, bits: u128, tcx: TyCtxt<'tcx>) -> &'tcx Const<'tcx> {
  let size = tcx.layout_of(ParamEnv::empty().and(ty)).unwrap().size;
  let val = ConstKind::Value(ConstValue::Scalar(Scalar::from_uint(bits, size)));
  tcx.mk_const(Const { ty, val })
}

pub fn get_tmnt<'a, 'tcx>(bbd: &'a BBD<'tcx>) -> &'a Tmnt<'tcx> { bbd.terminator.as_ref().unwrap() }

pub fn has_any_type(substs: &Substs) -> bool { substs.types().any(|_| true) }

pub fn only_ty<'tcx>(substs: &'tcx Substs<'tcx>) -> Ty<'tcx> {
  let tys = substs.types().collect::<Vec<_>>();
  assert!(tys.len() == 2 && format!("{:?}", tys[1]) == "std::alloc::Global");
  tys[0]
}

pub fn fun_of_fun_ty(fun_ty: Ty) -> DefId {
  match &fun_ty.kind() {
    TyK::FnDef(fun, _) => *fun,
    TyK::Closure(fun, _) => *fun,
    _ => panic!("unexpected type {} for a function type", fun_ty),
  }
}

pub fn substs_of_fun_ty(fun_ty: Ty<'_>) -> &'_ Substs<'_> {
  match &fun_ty.kind() {
    TyK::FnDef(_, substs) | TyK::Closure(_, substs) => substs,
    _ => panic!("unexpected type {} for a function type", fun_ty),
  }
}

pub fn sort_set<T: Ord>(mut set: Set<T>) -> Vec<T> {
  let mut vec = set.drain().collect::<Vec<_>>();
  vec.sort_unstable();
  vec
}
pub fn sort_map<K: Ord, V>(mut map: Map<K, V>) -> Vec<(K, V)> {
  let mut vec = map.drain().collect::<Vec<_>>();
  vec.sort_unstable_by(|(k1, _), (k2, _)| k1.cmp(k2));
  vec
}
