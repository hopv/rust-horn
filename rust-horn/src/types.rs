pub use rustc_apfloat::ieee::{
    Double as Float64, Half as Float16, Quad as Float128, Single as Float32,
};
pub use rustc_hir::{
    def_id::DefId,
    definitions::{DefPathData, DisambiguatedDefPathData},
    Mutability,
};
pub use rustc_middle::mir::{
    AggregateKind, BasicBlock, BasicBlockData, BasicBlocks, BinOp as MirBinOp, Body as MirBody,
    BorrowKind, ConstOperand, Local, LocalDecl, NullOp, Operand, Place, ProjectionElem, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind, UnOp as MirUnOp,
};
pub use rustc_middle::ty::{
    tls::with as with_tcx, AdtDef, ClosureKind, Const as TyConst, EarlyBinder, FieldDef, FloatTy,
    FnSig, FnSigTys, GenericArgs, GenericArgsRef, Instance, ParamEnv, TyCtxt, TyKind, VariantDef,
};
pub type Tys<'tcx> = <TyCtxt<'tcx> as rustc_type_ir::Interner>::Tys;
pub use rustc_session::config::EntryFnType;
pub use rustc_span::{source_map::Spanned, Symbol, DUMMY_SP};
pub use rustc_target::abi::{FieldIdx, Size, VariantIdx};

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
pub struct Map<K, V> {
    inner: HashMap<K, V>,
}

impl<K: Ord, V> Map<K, V> {
    pub fn into_sorted_vec(self) -> Vec<(K, V)> { sort_map(self.inner) }
}

impl<K, V> Default for Map<K, V> {
    fn default() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }
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

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq + ?Sized,
    {
        self.inner.remove(k)
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq + ?Sized,
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
pub struct OrderedSet<T> {
    inner: HashSet<T>,
}

impl<T: Ord> OrderedSet<T> {
    pub fn into_sorted_vec(self) -> Vec<T> { sort_set(self.inner) }
}

impl<T0: Eq + Hash> Extend<T0> for OrderedSet<T0> {
    #[inline]
    fn extend<I: IntoIterator<Item = T0>>(&mut self, iter: I) {
        <HashSet<T0> as Extend<T0>>::extend(&mut self.inner, iter);
    }
}

impl<T: Ord> IntoIterator for OrderedSet<T> {
    type Item = <Vec<T> as IntoIterator>::Item;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter { self.into_sorted_vec().into_iter() }
}

impl<T: Eq + Hash> OrderedSet<T> {
    pub fn new() -> Self {
        Self {
            inner: HashSet::<T>::new(),
        }
    }

    pub fn insert(&mut self, value: T) -> bool { self.inner.insert(value) }

    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.contains(value)
    }

    pub fn clear(&mut self) { self.inner.clear() }

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.remove(value)
    }

    pub fn is_subset(&self, other: &Self) -> bool { self.inner.is_subset(&other.inner) }

    pub fn retain<F>(&mut self, f: F)
    where F: FnMut(&T) -> bool {
        self.inner.retain(f);
    }
}

#[derive(Debug, Clone)]
pub struct Set<T> {
    dedup: HashSet<T>,
    container: Vec<T>,
}

impl<T> Set<T> {
    pub fn new() -> Self {
        Self {
            dedup: HashSet::new(),
            container: Vec::new(),
        }
    }

    pub fn into_inner_vec(self) -> Vec<T> { self.container }
}

impl<T0: Eq + Hash + Copy> Extend<T0> for Set<T0> {
    #[inline]
    fn extend<I: IntoIterator<Item = T0>>(&mut self, iter: I) {
        for item in iter {
            self.insert(item);
        }
    }
}

impl<T: Ord> IntoIterator for Set<T> {
    type Item = <Vec<T> as IntoIterator>::Item;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter { self.into_inner_vec().into_iter() }
}

impl<T: Eq + Hash + Copy> Set<T> {
    pub fn insert(&mut self, value: T) -> bool {
        let b = self.dedup.insert(value);
        if b {
            self.container.push(value);
        }
        b
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
                Some(FunTy {
                    def_id,
                    generic_args_ref: generic_args,
                })
            }
            _ => None,
        }
    }
}
