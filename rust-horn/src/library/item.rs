use std::sync::{Arc, Mutex};

use once_cell::sync::Lazy;
use rustc_hash::FxHashSet;
use rustc_index::{Idx, IndexVec};

use crate::analyze::data;
use crate::types::{DefId, TyCtxt};

use super::def_id_filter::DefIdFilter;
use super::impls;

pub struct Item {
    kind: ItemKind,
    filter: Option<DefIdFilter>,

    /// The index of the item that should be activated
    /// when this item is activated.
    activate_other: Option<ItemIdx>,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Intrinsic(IntrinsicKind),
    RawChcDef(RawChcDef),
    TypeAliasDef(TypeAliasDef),
    #[allow(dead_code)]
    FnDef(FnDef),
}

impl ItemKind {
    pub fn as_intrinsic(&self) -> Option<IntrinsicKind> {
        if let Self::Intrinsic(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_raw_chc_def(&self) -> Option<&RawChcDef> {
        if let Self::RawChcDef(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_type_alias_def(&self) -> Option<&TypeAliasDef> {
        if let Self::TypeAliasDef(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_fn_def(&self) -> Option<&FnDef> {
        if let Self::FnDef(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IntrinsicKind {
    BinOp(data::BinOp),
    UnOp(data::UnOp),
}

#[derive(Debug, Clone)]
pub struct TypeAliasDef {
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct RawChcDef {
    pub raw: String,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct FnDef {
    // pub body: syntax::Block,

    // FIXME: ad-hoc, temporary hack
    pub id: String,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ItemIdx(usize);

impl Idx for ItemIdx {
    fn new(idx: usize) -> Self { Self(idx) }

    fn index(self) -> usize { self.0 }
}

pub struct ItemStore {
    items: IndexVec<ItemIdx, Item>,
    activated_items: FxHashSet<ItemIdx>,
}

impl ItemStore {
    fn new() -> Self {
        let mut this = Self {
            items: IndexVec::new(),
            activated_items: FxHashSet::default(),
        };
        impls::provide_intrinsic_items(&mut this);
        this
    }
    pub fn register_item(&mut self, item: ItemKind, activate_other: Option<ItemIdx>) -> ItemIdx {
        self.items.push(Item {
            kind: item,
            filter: None,
            activate_other,
        })
    }
    pub fn register_filter(
        &mut self,
        filter: DefIdFilter,
        item: ItemKind,
        activate_other: Option<ItemIdx>,
    ) -> ItemIdx {
        self.items.push(Item {
            kind: item,
            filter: Some(filter),
            activate_other,
        })
    }
    fn search_by_filter(&self, tcx: TyCtxt, def_key: DefId) -> Option<ItemIdx> {
        self.items.iter_enumerated().find_map(|(index, item)| {
            if let Some(filter) = &item.filter {
                if filter.matches(tcx, def_key) {
                    Some(index)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }
    fn activate(&mut self, item: ItemIdx) {
        if self.activated_items.insert(item) {
            if let Some(other) = self.items[item].activate_other {
                self.activate(other);
            }
        }
    }
    fn search_and_activate(&mut self, tcx: TyCtxt, def_id: DefId) -> Option<ItemIdx> {
        let idx = self.search_by_filter(tcx, def_id);
        idx.inspect(|idx| self.activate(*idx))
    }

    fn activated_items(&self) -> impl Iterator<Item = &Item> {
        self.activated_items
            .iter()
            .map(move |&idx| &self.items[idx])
    }
    fn activated_chc_defs(&self) -> Vec<RawChcDef> {
        self.activated_items()
            .filter_map(|item| item.kind.as_raw_chc_def().cloned())
            .collect()
    }
}

static ITEM_STORE: Lazy<Arc<Mutex<ItemStore>>> =
    Lazy::new(|| Arc::new(Mutex::new(ItemStore::new())));

fn item_from_def_id(tcx: TyCtxt, def_id: DefId) -> Option<ItemKind> {
    let mut lock = ITEM_STORE.lock().unwrap();

    lock.search_and_activate(tcx, def_id)
        .map(|idx| lock.items[idx].kind.clone())
}

pub fn is_intrinsic(tcx: TyCtxt, def_id: DefId) -> Option<IntrinsicKind> {
    item_from_def_id(tcx, def_id).and_then(|item| item.as_intrinsic())
}

pub fn need_to_rename_ty(tcx: TyCtxt, def_id: DefId) -> Option<TypeAliasDef> {
    item_from_def_id(tcx, def_id).and_then(|item| item.as_type_alias_def().cloned())
}

pub fn need_to_replace_fn(tcx: TyCtxt, def_id: DefId) -> Option<FnDef> {
    item_from_def_id(tcx, def_id).and_then(|item| item.as_fn_def().cloned())
}

pub fn activated_chc_defs() -> Vec<RawChcDef> { ITEM_STORE.lock().unwrap().activated_chc_defs() }
