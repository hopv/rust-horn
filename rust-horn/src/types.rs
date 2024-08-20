pub use rustc_apfloat::ieee::{Double as Float64, Single as Float32};
pub use rustc_hir::{
    def_id::DefId,
    definitions::{DefPath, DefPathData, DisambiguatedDefPathData},
    Mutability,
};
pub use rustc_index::vec::IndexVec;
pub use rustc_middle::mir::{
    interpret::{ConstValue, Scalar},
    AggregateKind, BasicBlock, BasicBlockData, BinOp as MirBinOp, Body as MirBody, BorrowKind,
    Constant, ConstantKind, Field as FieldIdx, Local, LocalDecl, NullOp, Operand, Place,
    ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp as MirUnOp,
};
pub use rustc_middle::ty::{
    subst::{InternalSubsts as GenericArgs, Subst, SubstsRef as GenericArgsRef},
    tls::with as with_tcx,
    AdtDef, ClosureKind, Const as TyConst, ConstKind, FieldDef, FloatTy, FnSig, Instance, ParamEnv,
    ScalarInt, TyCtxt, TyKind, VariantDef,
};
pub use rustc_session::config::EntryFnType;
pub use rustc_span::Symbol;
pub type BasicBlockDatas<'tcx> = IndexVec<BasicBlock, BasicBlockData<'tcx>>;
pub use rustc_target::abi::{Size, VariantIdx};

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};
use std::{fmt::Display, ops::Index};

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

pub fn adt_is_box<'tcx>(
    adt_def: &'tcx AdtDef,
    generic_args: GenericArgsRef<'tcx>,
) -> Option<Ty<'tcx>> {
    if adt_def.is_box() {
        let tys = generic_args.types().collect::<Vec<_>>();
        assert!(tys.len() == 2 && format!("{:?}", tys[1]) == "std::alloc::Global");
        Some(Ty::new(tys[0]))
    } else {
        None
    }
}

fn sort_set<T: Ord>(set: HashSet<T>) -> Vec<T> {
    let mut vec = set.into_iter().collect::<Vec<_>>();
    vec.sort_unstable();
    vec
}

fn sort_map<K: Ord, V>(map: HashMap<K, V>) -> Vec<(K, V)> {
    let mut vec = map.into_iter().collect::<Vec<_>>();
    vec.sort_unstable_by(|(k1, _), (k2, _)| k1.cmp(k2));
    vec
}

#[derive(Debug, Clone)]
/// sorted map when iterated
pub struct Map<K, V> {
    inner: HashMap<K, V>,
}

impl<K: Ord, V> Map<K, V> {
    pub fn into_sorted_vec(self) -> Vec<(K, V)> { sort_map(self.inner) }
}

impl<K, V> Default for Map<K, V> {
    fn default() -> Self { Self { inner: HashMap::new() } }
}

impl<K, Q: ?Sized, V> Index<&Q> for Map<K, V>
where
    K: Eq + Hash + std::borrow::Borrow<Q>,
    Q: Eq + Hash,
{
    type Output = V;

    fn index(&self, index: &Q) -> &V { self.inner.index(index) }
}
impl<K: Ord, V> IntoIterator for Map<K, V> {
    type Item = <Vec<(K, V)> as IntoIterator>::Item;

    type IntoIter = <Vec<(K, V)> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter { self.into_sorted_vec().into_iter() }
}

impl<K: Ord + Hash, V> Map<K, V> {
    pub fn from_inner(inner: HashMap<K, V>) -> Self { Self { inner } }
    pub fn new() -> Self { Self::from_inner(HashMap::<K, V>::new()) }

    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        self.inner.remove(k)
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        self.inner.get(k)
    }

    pub fn entry(&mut self, key: K) -> std::collections::hash_map::Entry<'_, K, V> {
        self.inner.entry(key)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> { self.inner.insert(k, v) }

    pub fn is_empty(&self) -> bool { self.inner.is_empty() }

    pub fn drain(&mut self) -> std::collections::hash_map::Drain<'_, K, V> { self.inner.drain() }
}

#[derive(Debug, Clone)]
/// sorted set when iterated
pub struct Set<T> {
    inner: HashSet<T>,
}

impl<T: Ord> Set<T> {
    pub fn into_sorted_vec(self) -> Vec<T> { sort_set(self.inner) }
}

impl<T0: Eq + Hash> Extend<T0> for Set<T0> {
    #[inline]
    fn extend<I: IntoIterator<Item = T0>>(&mut self, iter: I) {
        <HashSet<T0> as Extend<T0>>::extend(&mut self.inner, iter);
    }
}

impl<T: Ord> IntoIterator for Set<T> {
    type Item = <Vec<T> as IntoIterator>::Item;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter { self.into_sorted_vec().into_iter() }
}

impl<T: Ord + Hash> Set<T> {
    pub fn new() -> Self { Self { inner: HashSet::<T>::new() } }

    pub fn insert(&mut self, value: T) -> bool { self.inner.insert(value) }

    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: Hash + Eq,
    {
        self.inner.contains(value)
    }

    pub fn clear(&mut self) { self.inner.clear() }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: Hash + Eq,
    {
        self.inner.remove(value)
    }

    pub fn is_subset(&self, other: &Self) -> bool { self.inner.is_subset(&other.inner) }

    pub fn retain<F>(&mut self, f: F)
    where F: FnMut(&T) -> bool {
        self.inner.retain(f);
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FunTy<'tcx> {
    pub def_id: DefId,
    pub generic_args_ref: GenericArgsRef<'tcx>,
}

impl<'tcx> Ty<'tcx> {
    pub fn as_fun_ty(self) -> Option<FunTy<'tcx>> {
        match *self.kind() {
            TyKind::FnDef(def_id, generic_args) | TyKind::Closure(def_id, generic_args) => {
                Some(FunTy { def_id, generic_args_ref: generic_args })
            }
            _ => None,
        }
    }
}
