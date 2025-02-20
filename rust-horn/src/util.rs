use crate::types::{
    BasicBlock, BasicBlockData, BasicBlocks, DefId, FieldIdx, GenericArgsRef, TyCtxt,
};

pub use rustc_middle::mir::{RETURN_PLACE, START_BLOCK};
pub use rustc_target::abi::FIRST_VARIANT;

pub const FLD0: FieldIdx = FieldIdx::from_u32(0);
pub const FLD1: FieldIdx = FieldIdx::from_u32(1);

/// Captures a lifetime.
pub trait Cap<'a> {}
impl<'a, T> Cap<'a> for T {}

/// Enumerates basic blocks that are not cleanup blocks.
pub fn enumerate_basicblock_datas<'a, 'tcx>(
    bbds: &'a BasicBlocks<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a BasicBlockData<'tcx>)> {
    bbds.iter_enumerated().filter(|(_, bbd)| !bbd.is_cleanup)
}

pub fn has_any_type(args: GenericArgsRef<'_>) -> bool { args.types().next().is_some() }

/// Returns `true` if the given [`DefId`] is the main function.
pub fn is_main(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.entry_fn(()).map(|(id, _)| id) == Some(def_id)
}
