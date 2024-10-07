use crate::analyze::data;

use super::{
    def_id_filter::{DefIdFilter, TyFilter},
    item::{FnDef, IntrinsicKind, ItemKind, ItemStore, RawChcDef, TypeAliasDef},
};

pub fn provide_intrinsic_items(store: &mut ItemStore) {
    store.register_filter(
        DefIdFilter::crate_name("core")
            .at_type_ns("ops")
            .at_type_ns("arith")
            .at_impl()
            .at_value_ns("add")
            .finish(),
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Add)),
        None,
    );
    store.register_filter(
        DefIdFilter::crate_name("core")
            .at_type_ns("cmp")
            .at_type_ns("impls")
            .at_impl()
            .at_value_ns("eq")
            .finish(),
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Eq)),
        None,
    );
    store.register_filter(
        DefIdFilter::crate_name("core")
            .at_type_ns("cmp")
            .at_type_ns("impls")
            .at_impl()
            .at_value_ns("ne")
            .finish(),
        ItemKind::Intrinsic(IntrinsicKind::BinOp(data::BinOp::Ne)),
        None,
    );
    store.register_filter(
        DefIdFilter::crate_name("core")
            .at_type_ns("num")
            .at_impl()
            .at_value_ns("abs")
            .finish(),
        ItemKind::Intrinsic(IntrinsicKind::UnOp(data::UnOp::Abs)),
        None,
    );
}
