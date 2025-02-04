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
    let self_str = "ChannelBuf<Int>";
    let channel_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
                raw: format!(
                    "(declare-datatypes (({self_str} 0)) ((par () ((insert (head Int) (tail {self_str})) (nilBuf)))))",
                ),
                phase: RawDefPhase::BeforeAdtDef,
        }),
        None,
    );
    let merge_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
            raw: format!(
                r#"(declare-fun MergeInt ({self_str} {self_str} {self_str}) Bool)
(assert (MergeInt nilBuf nilBuf nilBuf))
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

// FIXME: This is a temporary hack to provide the definition of
// `LockHistory` for `{local}::Mutex`. We will later
// invent a more general way to provide such definitions.
#[allow(dead_code)]
pub fn provide_optlib_mutex(store: &mut ItemStore) {
    let self_str = "LockHistory<Int>";
    let mutex_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
                raw: format!(
                    "(declare-datatypes (({self_str} 0)) ((par () ((insertLock (headHist ~Mut<Int>) (tailHist {self_str})) (nilHistory)))))",
                ),
                phase: RawDefPhase::BeforeAdtDef,
        }),
        None,
    );
    let merge_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
            raw: format!(
                r#"(declare-fun MergeLock ({self_str} {self_str} {self_str}) Bool)
(assert (MergeLock nilHistory nilHistory nilHistory))
(assert (forall ((x1 {self_str}) (x2 {self_str}) (x {self_str}) (n ~Mut<Int>))
  (=> (MergeLock x1 x2 x) (MergeLock (insertLock n x1) x2 (insertLock n x)))))
(assert (forall ((x1 {self_str}) (x2 {self_str}) (x {self_str}) (n ~Mut<Int>))
  (=> (MergeLock x1 x2 x) (MergeLock x1 (insertLock n x2) (insertLock n x)))))"#,
            ),
            phase: RawDefPhase::AfterDeclareSort,
        }),
        None,
    );
    let consistent_def = store.register_item(
        ItemKind::RawChcDef(RawChcDef {
            raw: format!(
                r#"(declare-fun Consistent (Int {self_str}) Bool)
(assert (forall ((init Int)) (Consistent init nilHistory)))
(assert (forall ((init Int) (init2 Int) (x {self_str}))
  (=> (Consistent init2 x) (Consistent init (insertLock (~mut<Int> init init2) x)))))"#,
            ),
            phase: RawDefPhase::AfterDeclareSort,
        }),
        None,
    );
    store.activate(mutex_def);
    store.activate(merge_def);
    store.activate(consistent_def);
}
