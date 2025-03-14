use crate::analyze::{
    data::{Cond, Env, Expr, MirAccess},
    Request,
};

pub struct State<'steal, 'tcx, 'env, 'conds, 'request> {
    pub mir_access: MirAccess<'steal, 'tcx>,
    pub env: &'env mut Env<'tcx>,
    pub conds: &'conds mut Vec<Cond<'tcx>>,
    pub def_request: &'request mut Request<'tcx>,
}

pub type HardcodedImplFnPtrTy =
    for<'tcx> fn(state: State<'_, 'tcx, '_, '_, '_>, args: &[Expr<'tcx>]) -> Option<Expr<'tcx>>;
