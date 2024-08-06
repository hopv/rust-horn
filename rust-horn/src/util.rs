use crate::types::{
    BasicBlock, BasicBlockData, BasicBlockDatas, DefId, FieldIdx, GenericArgsRef, Local, MirBody,
    Terminator, Ty, TyCtxt, TyKind, VariantIdx,
};

pub const BB0: BasicBlock = BasicBlock::from_u32(0);
pub const _0: Local = Local::from_u32(0);
pub const VRT0: VariantIdx = VariantIdx::from_u32(0);
pub const FLD0: FieldIdx = FieldIdx::from_u32(0);
pub const FLD1: FieldIdx = FieldIdx::from_u32(1);

/* captures a lifetime */
pub trait Cap<'a> {}
impl<'a, T> Cap<'a> for T {}

pub fn enumerate_bbds<'a, 'tcx>(
    bbds: &'a BasicBlockDatas<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a BasicBlockData<'tcx>)> {
    bbds.iter()
        .enumerate()
        .filter(|(_, bbd)| !bbd.is_cleanup)
        .map(|(i, bbd)| (BasicBlock::from(i), bbd))
}

pub fn enumerate_mirs<'tcx>(tcx: TyCtxt<'tcx>) -> impl Iterator<Item = (DefId, &MirBody<'tcx>)> {
    tcx.mir_keys(())
        .iter()
        .map(|fun| fun.to_def_id())
        .filter(move |&fun| {
            tcx.def_path(fun).data.iter().all(|elem| &elem.data.to_string() != "{{constructor}}")
        })
        .map(move |fun| {
            let mir = tcx.optimized_mir(fun);
            (fun, mir)
        })
}

pub fn get_terminator<'a, 'tcx>(bbd: &'a BasicBlockData<'tcx>) -> &'a Terminator<'tcx> {
    bbd.terminator.as_ref().unwrap()
}

pub fn has_any_type(generic_args: GenericArgsRef<'_>) -> bool {
    generic_args.types().next().is_some()
}

impl<'tcx> Ty<'tcx> {
    pub fn fun_of_fun_ty(self) -> DefId {
        match &self.kind() {
            TyKind::FnDef(fun, _) | TyKind::Closure(fun, _) => *fun,
            _ => panic!("unexpected type {} for a function type", self.ty),
        }
    }

    pub fn substs_of_fun_ty(self) -> GenericArgsRef<'tcx> {
        match &self.kind() {
            TyKind::FnDef(_, generic_args) | TyKind::Closure(_, generic_args) => generic_args,
            _ => panic!("unexpected type {} for a function type", self.ty),
        }
    }
}
