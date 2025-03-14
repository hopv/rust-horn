use crate::analyze::data::{self, Cond};

use super::{
    def_id_filter::DefIdFilter,
    item::{IntrinsicKind, ItemKind, ItemStore},
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

pub fn provide_stdlib_items(store: &mut ItemStore) {
    store.register_filter(
        DefIdFilter::crate_name("core")
            .at_type_ns("mem")
            .at_impl()
            .at_value_ns("swap")
            .finish(),
        ItemKind::HardcodedImpl(|state, args| {
            let (x, x_) = args[0].decompose_mut();
            let (y, y_) = args[1].decompose_mut();
            state.conds.push(Cond::Eq { tgt: y_, src: x });
            state.conds.push(Cond::Eq { tgt: x_, src: y });

            None
        }),
        None,
    );
}
