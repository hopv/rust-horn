//! find `DefPath` the implementation of which we want to override.

use crate::types::{DefPath, DefPathData, DisambiguatedDefPathData, Symbol, TyCtxt};

pub struct DefPathFilter {
    data: Vec<DefPathDataFilter>,
    crate_name: Symbol,
}

impl DefPathFilter {
    pub fn crate_name(string: &str) -> DefPathFilterBuilder {
        DefPathFilterBuilder(Self { data: Vec::new(), crate_name: Symbol::intern(string) })
    }
}

pub struct DefPathFilterBuilder(DefPathFilter);

impl DefPathFilterBuilder {
    #[inline]
    fn add(mut self, component: DefPathDataFilter) -> Self {
        self.0.data.push(component);
        self
    }
    #[inline]
    pub fn at_type_ns(self, string: &str) -> Self {
        self.add(DefPathDataFilter::TypeNs(SymbolFilter(Symbol::intern(string))))
    }
    #[inline]
    pub fn at_value_ns(self, string: &str) -> Self {
        self.add(DefPathDataFilter::ValueNs(SymbolFilter(Symbol::intern(string))))
    }
    #[inline]
    pub fn at_impl(self) -> Self { self.add(DefPathDataFilter::Impl) }
    #[inline]
    pub fn finish(self) -> DefPathFilter { self.0 }
}

impl DefPathFilter {
    pub fn matches(&self, tcx: TyCtxt, def_path: &DefPath) -> bool {
        let crate_num = def_path.krate;
        if crate_num.as_def_id().is_local() {
            // in this case we do not want to match since it is user defined crate.
            return false;
        }
        let crate_name = tcx.cstore_untracked().crate_name(crate_num);
        if self.crate_name != crate_name {
            return false;
        }
        for (component, target) in self.data.iter().zip(def_path.data.iter()) {
            if component.filtered_out(*target) {
                return false;
            }
        }
        true
    }
}

trait Filter {
    type Target;
    fn filtered_out(&self, target: Self::Target) -> bool;
}

impl<T: Copy + Eq> Filter for T {
    type Target = T;

    fn filtered_out(&self, target: Self::Target) -> bool { self != &target }
}

#[derive(Debug)]
pub enum DefPathDataFilter {
    TypeNs(SymbolFilter),
    ValueNs(SymbolFilter),
    Impl,
}

impl Filter for DefPathDataFilter {
    type Target = DisambiguatedDefPathData;

    fn filtered_out(&self, target: Self::Target) -> bool {
        // we skip `target.disambiguator` for filtering
        // because it can easily be changed.
        match (self, target.data) {
            (DefPathDataFilter::TypeNs(l), DefPathData::TypeNs(r)) => l.filtered_out(r),
            (DefPathDataFilter::ValueNs(l), DefPathData::ValueNs(r)) => l.filtered_out(r),
            (DefPathDataFilter::Impl, DefPathData::Impl) => false,
            _ => true,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SymbolFilter(Symbol);

impl Filter for SymbolFilter {
    type Target = Symbol;

    fn filtered_out(&self, target: Self::Target) -> bool { self.0.filtered_out(target) }
}
