//! find `DefId` of the implementation which we want to override.

use std::sync::{Arc, Mutex};

use once_cell::sync::Lazy;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::types::{DefPathData, DisambiguatedDefPathData, Symbol, Ty, TyCtxt, TyKind};

#[derive(Debug)]
pub struct DefIdFilter {
    data: Vec<DefPathDataFilter>,
    crate_name: Symbol,
}

impl DefIdFilter {
    pub fn crate_name(string: &str) -> DefIdFilterBuilder {
        DefIdFilterBuilder(Self {
            data: Vec::new(),
            crate_name: Symbol::intern(string),
        })
    }
}

pub struct DefIdFilterBuilder(DefIdFilter);

impl DefIdFilterBuilder {
    #[inline]
    fn add(mut self, component: DefPathDataFilter) -> Self {
        self.0.data.push(component);
        self
    }
    #[inline]
    pub fn at_type_ns(self, string: &str) -> Self {
        self.add(DefPathDataFilter::TypeNs(SymbolFilter(Symbol::intern(
            string,
        ))))
    }
    #[inline]
    pub fn at_value_ns(self, string: &str) -> Self {
        self.add(DefPathDataFilter::ValueNs(SymbolFilter(Symbol::intern(
            string,
        ))))
    }
    #[inline]
    pub fn at_impl(self) -> Self { self.add(DefPathDataFilter::Impl(Default::default())) }
    #[inline]
    pub fn at_impl_of(self) -> DefIdFilterImplBuilder { DefIdFilterImplBuilder::new(self) }
    #[inline]
    pub fn finish(self) -> DefIdFilter { self.0 }
}

pub struct DefIdFilterImplBuilder {
    parent: DefIdFilterBuilder,
    self_ty: Option<TyFilter>,
    trait_ref: Option<DefIdFilter>,
}

impl DefIdFilterImplBuilder {
    fn new(builder: DefIdFilterBuilder) -> Self {
        Self {
            parent: builder,
            self_ty: None,
            trait_ref: None,
        }
    }
    pub fn self_ty(mut self, filter: TyFilter) -> Self {
        assert!(self.self_ty.is_none(), "self_ty is already set");
        self.self_ty = Some(filter);
        self
    }

    pub fn trait_ref(mut self, filter: DefIdFilter) -> Self {
        assert!(self.trait_ref.is_none(), "trait_ref is already set");
        self.trait_ref = Some(filter);
        self
    }
    #[inline]
    pub fn finish_impl(self) -> DefIdFilterBuilder {
        self.parent.add(DefPathDataFilter::Impl(ImplFilter {
            self_ty: self.self_ty.map(Box::new),
            trait_ref: self.trait_ref.map(Box::new),
        }))
    }
}

trait Filter<'tcx> {
    type Target;
    fn filter(&self, tcx: TyCtxt<'tcx>, target: &Self::Target) -> bool;
}

impl DefIdFilter {
    pub fn matches(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool { self.filter(tcx, &def_id) }
}

impl<'tcx> Filter<'tcx> for DefIdFilter {
    type Target = DefId;

    fn filter(&self, tcx: TyCtxt<'tcx>, def_id: &Self::Target) -> bool {
        static CACHE: Lazy<Arc<Mutex<RichDefPathCache>>> =
            Lazy::new(|| Arc::new(Mutex::new(RichDefPathCache::default())));
        let crate_num = def_id.krate;
        if def_id.is_local() {
            // in this case we do not want to match since it is user defined crate.
            return false;
        }
        let crate_name = tcx.crate_name(crate_num);
        if self.crate_name != crate_name {
            return false;
        }
        let rich_def_path = CACHE.lock().unwrap().get_or_insert(tcx, *def_id);
        for (component, target) in self.data.iter().zip(rich_def_path.data.iter()) {
            if !component.filter(tcx, target) {
                return false;
            }
        }
        true
    }
}

#[derive(Default)]
struct RichDefPathCache {
    cache: FxHashMap<DefId, RichDefPath>,
}

impl RichDefPathCache {
    fn get_or_insert(&mut self, tcx: TyCtxt, def_id: DefId) -> RichDefPath {
        self.cache
            .entry(def_id)
            .or_insert_with(|| RichDefPath::make(tcx, def_id))
            .clone()
    }
}

#[derive(Debug, Clone)]
struct RichDefPath {
    data: Vec<RichDefPathData>,
}
#[derive(Debug, Clone, Copy)]
struct RichDefPathData {
    disambiguated_data: DisambiguatedDefPathData,
    /// def_id of the item, which cannot be obtained via `DefPath`.
    def_id: DefId,
}

impl RichDefPath {
    /// Similar to `DefPath::make`, but also stores `DefId` for each component.
    fn make(tcx: TyCtxt, mut def_id: DefId) -> Self {
        let mut data = vec![];
        let mut index = Some(def_id.index);
        loop {
            let p = index.unwrap();
            def_id = DefId { index: p, ..def_id };
            let key = tcx.def_key(def_id);
            match key.disambiguated_data.data {
                DefPathData::CrateRoot => {
                    assert!(key.parent.is_none());
                    break;
                }
                _ => {
                    data.push(RichDefPathData {
                        disambiguated_data: key.disambiguated_data,
                        def_id,
                    });
                    index = key.parent;
                }
            }
        }
        data.reverse();
        Self { data }
    }
}

#[derive(Debug)]
pub enum DefPathDataFilter {
    TypeNs(SymbolFilter),
    ValueNs(SymbolFilter),
    Impl(ImplFilter),
}

#[derive(Debug, Default)]
pub struct ImplFilter {
    self_ty: Option<Box<TyFilter>>,
    trait_ref: Option<Box<DefIdFilter>>,
}

impl<'tcx> Filter<'tcx> for DefPathDataFilter {
    type Target = RichDefPathData;

    fn filter(&self, tcx: TyCtxt<'tcx>, target: &Self::Target) -> bool {
        // we skip `target.disambiguator` for filtering
        // because it can easily be changed.
        match (self, &target.disambiguated_data.data) {
            (DefPathDataFilter::TypeNs(l), DefPathData::TypeNs(r)) => l.filter(tcx, r),
            (DefPathDataFilter::ValueNs(l), DefPathData::ValueNs(r)) => l.filter(tcx, r),
            (DefPathDataFilter::Impl(ImplFilter { self_ty, trait_ref }), DefPathData::Impl) => {
                if let Some(self_ty) = self_ty {
                    let ty = tcx.type_of(target.def_id).instantiate_identity();
                    if !self_ty.filter(tcx, &Ty::new(ty)) {
                        return false;
                    }
                }
                if let Some(trait_ref) = trait_ref {
                    if let Some(lhs_trait_ref) = tcx.impl_trait_ref(target.def_id) {
                        if !trait_ref.filter(tcx, &lhs_trait_ref.instantiate_identity().def_id) {
                            return false;
                        }
                    } else {
                        return false;
                    };
                }
                true
            }
            _ => false,
        }
    }
}

#[derive(Debug)]
pub enum TyFilter {
    Adt(DefIdFilter),
}

impl<'tcx> Filter<'tcx> for TyFilter {
    type Target = Ty<'tcx>;

    fn filter(&self, tcx: TyCtxt<'tcx>, target: &Self::Target) -> bool {
        match (self, target.kind()) {
            (TyFilter::Adt(filter), TyKind::Adt(adt_def, ..)) => filter.filter(tcx, &adt_def.did()),
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SymbolFilter(Symbol);

impl<'tcx> Filter<'tcx> for SymbolFilter {
    type Target = Symbol;

    fn filter(&self, tcx: TyCtxt<'tcx>, target: &Self::Target) -> bool {
        self.0.filter(tcx, target)
    }
}

impl<'tcx> Filter<'tcx> for Symbol {
    type Target = Symbol;

    fn filter(&self, _tcx: TyCtxt<'tcx>, target: &Self::Target) -> bool { self == target }
}
