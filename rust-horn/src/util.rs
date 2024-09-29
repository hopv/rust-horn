use crate::types::{
    BasicBlock, BasicBlockData, BasicBlocks, FieldIdx, GenericArgsRef, Local, Terminator,
    VariantIdx,
};

pub const BB0: BasicBlock = BasicBlock::from_u32(0);
pub const _0: Local = Local::from_u32(0);
pub const VRT0: VariantIdx = VariantIdx::from_u32(0);
pub const FLD0: FieldIdx = FieldIdx::from_u32(0);
pub const FLD1: FieldIdx = FieldIdx::from_u32(1);

/// Captures a lifetime.
pub trait Cap<'a> {}
impl<'a, T> Cap<'a> for T {}

pub fn enumerate_bbds<'a, 'tcx>(
    bbds: &'a BasicBlocks<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a BasicBlockData<'tcx>)> {
    bbds.iter()
        .enumerate()
        .filter(|(_, bbd)| !bbd.is_cleanup)
        .map(|(i, bbd)| (BasicBlock::from(i), bbd))
}

pub fn get_terminator<'a, 'tcx>(bbd: &'a BasicBlockData<'tcx>) -> &'a Terminator<'tcx> {
    bbd.terminator.as_ref().unwrap()
}

pub fn has_any_type(generic_args: GenericArgsRef<'_>) -> bool {
    generic_args.types().next().is_some()
}
