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
pub type Tys<'tcx> = Vec<Ty<'tcx>>;
pub use rustc_session::config::EntryFnType;
pub use rustc_span::{source_map::Spanned, Symbol, DUMMY_SP};
pub use rustc_target::abi::{FieldIdx, Size, VariantIdx};

use std::fmt::Display;
use std::{collections::HashSet, hash::Hash};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ty<'tcx> {
    ty: rustc_middle::ty::Ty<'tcx>,
    kind: RhTyKind<'tcx>,
}

impl<'tcx> Display for Ty<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.ty.fmt(f) }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Types in Rust-Horn.
pub enum RhTyKind<'tcx> {
    Bool,
    Int,
    Float,

    /// An ADT. `Box` no longer occurs in this variant.
    Adt {
        def: AdtDef<'tcx>,
        args: GenericArgsRef<'tcx>,
    },

    Fn(FunTy<'tcx>),
    Tuple {
        elems: Tys<'tcx>,
    },
    RefMut {
        ty: Box<Ty<'tcx>>,
    },
    Transparent {
        kind: TransparentKind,
        ty: Box<Ty<'tcx>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TransparentKind {
    Box,
    RefImmut,
}

impl<'tcx> RhTyKind<'tcx> {
    fn from_raw(ty: rustc_middle::ty::Ty<'tcx>) -> Self {
        if ty.is_box() {
            return Self::Transparent {
                kind: TransparentKind::Box,
                ty: Box::new(Ty::new(ty.boxed_ty())),
            };
        }
        match ty.kind() {
            TyKind::Bool => Self::Bool,
            TyKind::Int(..) | TyKind::Uint(..) => Self::Int,
            TyKind::Float(..) => Self::Float,
            TyKind::Adt(def, args) => Self::Adt { def: *def, args },
            TyKind::Ref(_, ty, Mutability::Not) => Self::Transparent {
                kind: TransparentKind::RefImmut,
                ty: Box::new(Ty::new(*ty)),
            },
            TyKind::Ref(_, ty, Mutability::Mut) => Self::RefMut {
                ty: Box::new(Ty::new(*ty)),
            },
            TyKind::FnDef(def_id, generic_args_ref) | TyKind::Closure(def_id, generic_args_ref) => {
                Self::Fn(FunTy {
                    def_id: *def_id,
                    generic_args_ref,
                })
            }
            TyKind::Tuple(elems) => Self::Tuple {
                elems: elems.into_iter().map(Ty::new).collect(),
            },
            _ => panic!("{ty} is not supported yet"),
        }
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new(ty: rustc_middle::ty::Ty<'tcx>) -> Self {
        let kind = RhTyKind::from_raw(ty);
        Self { ty, kind }
    }

    /// Returns `true` if the kind is [`RefMut`].
    ///
    /// [`RefMut`]: RhTyKind::RefMut
    #[must_use]
    pub fn is_ref_mut(&self) -> bool { matches!(self.kind, RhTyKind::RefMut { .. }) }

    pub fn is_unit(&self) -> bool { self.ty.is_unit() }

    pub fn kind(&self) -> &'_ RhTyKind<'tcx> { &self.kind }
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct FunTy<'tcx> {
    pub def_id: DefId,
    pub generic_args_ref: GenericArgsRef<'tcx>,
}

impl<'tcx> Ty<'tcx> {
    pub fn as_fun_ty(&self) -> Option<FunTy<'tcx>> {
        if let RhTyKind::Fn(fun_ty) = self.kind {
            Some(fun_ty)
        } else {
            None
        }
    }
}
