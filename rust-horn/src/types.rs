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
    tls::with as with_tcx, AdtDef, ClosureKind, Const as TyConst, FieldDef, FloatTy, FnSig,
    FnSigTys, GenericArgs, GenericArgsRef, Instance, ParamEnv, TyCtxt, TyKind, VariantDef,
};
pub type Tys<'tcx> = <TyCtxt<'tcx> as rustc_type_ir::Interner>::Tys;
pub use rustc_session::config::EntryFnType;
pub use rustc_span::{source_map::Spanned, Symbol, DUMMY_SP};
pub use rustc_target::abi::{FieldIdx, Size, VariantIdx};

use std::fmt::Display;
use std::{collections::HashSet, hash::Hash};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Ty<'tcx> {
    pub ty: rustc_middle::ty::Ty<'tcx>,
}

impl<'tcx> Display for Ty<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.ty.fmt(f) }
}

impl<'tcx> Ty<'tcx> {
    pub fn new(ty: rustc_middle::ty::Ty<'tcx>) -> Self { Self { ty } }

    pub fn as_boxed_ty(self) -> Option<Self> {
        if self.is_box() {
            Some(Ty::new(self.boxed_ty()))
        } else {
            None
        }
    }
}

impl<'tcx> std::ops::Deref for Ty<'tcx> {
    type Target = rustc_middle::ty::Ty<'tcx>;

    fn deref(&self) -> &Self::Target { &self.ty }
}

fn sort_set<T: Ord>(set: HashSet<T>) -> Vec<T> {
    let mut vec = set.into_iter().collect::<Vec<_>>();
    vec.sort_unstable();
    vec
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
