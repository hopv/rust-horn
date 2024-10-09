use crate::analyze::data::{self, Cond};

use super::{
    def_id_filter::DefIdFilter,
    item::{IntrinsicKind, ItemKind, ItemStore, RawChcDef},
    RawDefPhase,
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

// FIXME: This is a temporary hack to provide the definition of
// `ChannelBuf` for `{local}::Sender`. We will later
// invent a more general way to provide such definitions.
pub fn provide_optlib_channel(store: &mut ItemStore) {
    let self_str = "ChannelBuf<int>";
    let channel_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
                raw: format!(
                    "(declare-datatypes (({self_str} 0)) ((par () ((insert (head Int) (tail {self_str})) (nil)))))",
                ),
                phase: RawDefPhase::BeforeAdtDef,
        }),
        None,
    );
    let merge_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
            raw: format!(
                r#"(declare-fun MergeInt ({self_str} {self_str} {self_str}) Bool)
(assert (MergeInt nil nil nil))
(assert (forall ((x1 {self_str}) (x2 {self_str}) (x {self_str}) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt (insert n x1) x2 (insert n x)))))
(assert (forall ((x1 {self_str}) (x2 {self_str}) (x {self_str}) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt x1 (insert n x2) (insert n x)))))"#,
            ),
            phase: RawDefPhase::AfterDeclareSort,
        }),
        None,
    );
    store.activate(channel_def);
    store.activate(merge_def);
}
