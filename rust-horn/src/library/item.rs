use std::cell::RefCell;

use crate::analyze::data;
use crate::types::{DefId, TyCtxt};

use super::def_path_filter::DefPathFilter;
use super::{impls, syntax};

pub struct Item {
    kind: ItemKind,
    filter: Option<DefPathFilter>,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Intrinsic(IntrinsicKind),
    TypeDef(TypeDef),
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
}

#[derive(Debug, Clone, Copy)]
pub enum IntrinsicKind {
    BinOp(data::BinOp),
    UnOp(data::UnOp),
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub kind: TypeDefKind,
}

impl TypeDef {
    pub fn new(kind: TypeDefKind) -> Self { Self { kind } }
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    RawChc { raw: String },
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub body: syntax::Block,
}

pub struct ItemStore {
    items: Vec<Item>,
}

impl ItemStore {
    fn new() -> Self {
        let mut this = Self { items: Vec::new() };
        impls::provide_intrinsic_items(&mut this);
        this
    }
    pub fn register(&mut self, item: ItemKind) {
        self.items.push(Item {
            kind: item,
            filter: None,
        });
    }
    pub fn register_filtered(&mut self, item: ItemKind, filter: DefPathFilter) {
        self.items.push(Item {
            kind: item,
            filter: Some(filter),
        });
    }
}

thread_local! {
    static ITEM_FILTER_MAP: RefCell<ItemStore> = RefCell::new(ItemStore::new());
}

pub fn item_from_def_id(tcx: TyCtxt, def_id: DefId) -> Option<ItemKind> {
    let def_path = tcx.def_path(def_id);
    ITEM_FILTER_MAP.with(|r| {
        r.borrow().items.iter().find_map(|item| {
            if let Some(filter) = &item.filter {
                if filter.matches(tcx, &def_path) {
                    Some(item.kind.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
    })
}

pub fn is_intrinsic(tcx: TyCtxt, def_id: DefId) -> Option<IntrinsicKind> {
    item_from_def_id(tcx, def_id).and_then(|item| item.as_intrinsic())
}
