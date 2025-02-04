use std::borrow::Cow;
use std::collections::HashMap;
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
    #[allow(dead_code)]
    TypeDef(TypeDef),
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

    pub fn as_type_def(&self) -> Option<&TypeDef> {
        if let Self::TypeDef(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[allow(dead_code)]
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
pub struct TypeDef {
    pub alias: Option<String>,
    pub attrs: HashMap<TypeAttrId, TypeAttrValue>,
}

pub type TypeAttrId = Cow<'static, str>;

#[derive(Debug, Clone)]
pub enum TypeAttrValue {
    Int(i32),
    Str(String),
    Bool(bool),
}

impl TypeAttrValue {
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RawDefPhase {
    BeforeAdtDef,
    AfterDeclareSort,
}

#[derive(Debug, Clone)]
pub struct RawChcDef {
    pub raw: String,
    pub phase: RawDefPhase,
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
    activated_items: Arc<Mutex<FxHashSet<ItemIdx>>>,
}

impl ItemStore {
    fn new() -> Self {
        let mut this = Self {
            items: IndexVec::new(),
            activated_items: Arc::new(Mutex::new(FxHashSet::default())),
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
    pub fn activate(&self, item: ItemIdx) {
        let b = self.activated_items.lock().unwrap().insert(item);
        if b {
            if let Some(other) = self.items[item].activate_other {
                self.activate(other);
            }
        }
    }
    fn search_and_activate(&self, tcx: TyCtxt, def_id: DefId) -> Option<ItemIdx> {
        let idx = self.search_by_filter(tcx, def_id);
        idx.inspect(|idx| self.activate(*idx))
    }

    fn activated_chc_defs(&self) -> Vec<&RawChcDef> {
        self.activated_items
            .lock()
            .unwrap()
            .iter()
            .map(move |&idx| &self.items[idx])
            .filter_map(|item| item.kind.as_raw_chc_def())
            .collect()
    }
}

static ITEM_STORE: Lazy<ItemStore> = Lazy::new(ItemStore::new);

fn item_from_def_id(tcx: TyCtxt, def_id: DefId) -> Option<&'static ItemKind> {
    ITEM_STORE
        .search_and_activate(tcx, def_id)
        .map(|idx| &ITEM_STORE.items[idx].kind)
}

pub fn is_intrinsic(tcx: TyCtxt, def_id: DefId) -> Option<IntrinsicKind> {
    item_from_def_id(tcx, def_id).and_then(ItemKind::as_intrinsic)
}

pub fn need_to_rename_ty(tcx: TyCtxt, def_id: DefId) -> Option<&'static str> {
    item_from_def_id(tcx, def_id)
        .and_then(|item| item.as_type_def())
        .and_then(|def| def.alias.as_deref())
}

#[allow(dead_code)]
pub fn need_to_replace_fn(tcx: TyCtxt, def_id: DefId) -> Option<&'static FnDef> {
    item_from_def_id(tcx, def_id).and_then(|item| item.as_fn_def())
}

pub fn activated_chc_defs() -> Vec<&'static RawChcDef> { ITEM_STORE.activated_chc_defs() }
