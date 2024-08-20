use std::cell::RefCell;

use crate::analyze::data;
use crate::types::{DefId, TyCtxt};

use super::def_path_filter::DefPathFilter;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum IntrinsicKind {
    BinOp(data::BinOp),
    UnOp(data::UnOp),
}

thread_local! {
    static INTRINSIC_FILTER_MAP: RefCell<Vec<(IntrinsicKind, DefPathFilter)>> = RefCell::new(vec![
        (IntrinsicKind::BinOp(data::BinOp::Add), DefPathFilter::crate_name("core").at_type_ns("ops").at_type_ns("arith").at_impl().at_value_ns("add").finish()),
    ]);
}

pub fn is_intrinsic(tcx: TyCtxt, def_id: DefId) -> Option<IntrinsicKind> {
    let def_path = tcx.def_path(def_id);
    INTRINSIC_FILTER_MAP.with(|r| {
        r.borrow().iter().find_map(|(k, v)| if v.matches(tcx, &def_path) { Some(*k) } else { None })
    })
}
