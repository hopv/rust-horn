use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::mir::{
  BasicBlock as BB, BasicBlockData as BBD, BodyAndCache, Field as FldIdx, Local, Terminator as Tmnt,
};
use rustc::ty::layout::VariantIdx as VrtIdx;
use rustc::ty::subst::InternalSubsts as Substs;
use rustc::ty::{Const, ConstKind, FieldDef as FldDef, ParamEnv, Ty, TyCtxt, TyKind as TyK};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_index::vec::IndexVec;
use std::cmp::Ord;
use std::collections::{HashMap as Map, HashSet as Set};

pub const BB0: BB = BB::from_u32_const(0);
pub const _0: Local = Local::from_u32_const(0);
pub const VRT0: VrtIdx = VrtIdx::from_u32_const(0);
pub const FLD0: FldIdx = FldIdx::from_u32_const(0);
pub const FLD1: FldIdx = FldIdx::from_u32_const(1);

pub type BBDs<'tcx> = IndexVec<BB, BBD<'tcx>>;

/* captures a lifetime */
pub trait Cap<'a> {}
impl<'a, T> Cap<'a> for T {}

pub fn enumerate_bbds<'a, 'tcx>(bbds: &'a BBDs<'tcx>) -> impl Iterator<Item = (BB, &'a BBD<'tcx>)> {
  bbds.iter().enumerate().filter(|(_, bbd)| !bbd.is_cleanup).map(|(i, bbd)| (BB::from(i), bbd))
}

pub fn enumerate_mirs<'tcx>(
  tcx: TyCtxt<'tcx>,
) -> impl Iterator<Item = (DefId, &BodyAndCache<'tcx>)> {
  tcx
    .mir_keys(LOCAL_CRATE)
    .iter()
    .filter(move |&&fun| {
      tcx.def_path(fun).data.iter().all(|elem| &elem.data.to_string() != "{{constructor}}")
    })
    .map(move |&fun| {
      let mir = tcx.optimized_mir(fun);
      (fun, mir)
    })
}

pub fn enumerate_fld_defs(fld_defs: &Vec<FldDef>) -> impl Iterator<Item = (FldIdx, &FldDef)> {
  fld_defs.iter().enumerate().map(|(i, fld_def)| (FldIdx::from(i), fld_def))
}

pub fn bits_to_cnst<'tcx>(ty: Ty<'tcx>, bits: u128, tcx: TyCtxt<'tcx>) -> &'tcx Const<'tcx> {
  let size = tcx.layout_of(ParamEnv::empty().and(ty)).unwrap().size.bytes() as u8;
  tcx.mk_const(Const {
    ty,
    val: ConstKind::Value(ConstValue::Scalar(Scalar::Raw { data: bits, size })),
  })
}

pub fn get_tmnt<'a, 'tcx>(bbd: &'a BBD<'tcx>) -> &'a Tmnt<'tcx> { bbd.terminator.as_ref().unwrap() }

pub fn has_any_type(substs: &Substs) -> bool { substs.types().any(|_| true) }

pub fn only_ty<'tcx>(substs: &'tcx Substs<'tcx>) -> Ty<'tcx> {
  let mut it = substs.types();
  if let Some(ty) = it.next_back() {
    assert_eq!(None, it.next_back(), "multiple types found");
    return ty;
  }
  panic!("no type found");
}

pub fn fun_of_fun_ty(fun_ty: Ty) -> DefId {
  match &fun_ty.kind {
    TyK::FnDef(fun, _) => *fun,
    TyK::Closure(fun, _) => *fun,
    _ => panic!("unexpected type {} for a function type", fun_ty),
  }
}

pub fn substs_of_fun_ty<'tcx>(fun_ty: Ty<'tcx>) -> &'tcx Substs<'tcx> {
  match &fun_ty.kind {
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
