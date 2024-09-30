use crate::analyze::data;

use super::{
    def_path_filter::DefPathFilter,
    item::{IntrinsicKind, ItemKind, ItemStore, TypeDef, TypeDefKind},
};

pub fn provide_intrinsic_items(store: &mut ItemStore) {
    store.register_filtered(
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Add)),
        DefPathFilter::crate_name("core")
            .at_type_ns("ops")
            .at_type_ns("arith")
            .at_impl()
            .at_value_ns("add")
            .finish(),
    );
    store.register_filtered(
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Eq)),
        DefPathFilter::crate_name("core")
            .at_type_ns("cmp")
            .at_type_ns("impls")
            .at_impl()
            .at_value_ns("eq")
            .finish(),
    );
    store.register_filtered(
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Ne)),
        DefPathFilter::crate_name("core")
            .at_type_ns("cmp")
            .at_type_ns("impls")
            .at_impl()
            .at_value_ns("ne")
            .finish(),
    );
    store.register_filtered(
        ItemKind::Intrinsic(IntrinsicKind::UnOp(data::UnOp::Abs)),
        DefPathFilter::crate_name("core")
            .at_type_ns("num")
            .at_impl()
            .at_value_ns("abs")
            .finish(),
    );
}
