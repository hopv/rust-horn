use crate::library::{self, IntrinsicKind};
use crate::prettify::pr_fun_name;
use crate::types::{
    BasicBlock, DefId, EntryFnType, FieldDef, FieldIdx, FunTy, Instance, Local, Mutability,
    Operand, OrderedSet, ParamEnv, Place, Rvalue, Spanned, Statement, StatementKind,
    TerminatorKind, Ty, TyCtxt, TyKind, Tys, VariantDef,
};
use crate::util::{is_main, BB0, _0};

pub mod graph;
use graph::Basic;

pub mod data;
use data::{
    set_tag, AssignExt, Cond, Const, DropExt, End, Env, Expr, GetTypeExt, Int, MirAccess,
    MirAccessCtxExt, Path, ReadExprCtxExt, ReadExprExt, ReadExprMutExt, Var,
};
use indexmap::{IndexMap, IndexSet};

#[derive(Debug)]
pub struct Prerule<'tcx> {
    pub init_env: Env<'tcx>,
    pub conds: Vec<Cond<'tcx>>,
    pub end: End<'tcx>,
}
#[derive(Debug)]
pub struct Rule<'tcx> {
    pub vars: Vec<(Var, Ty<'tcx>)>,
    pub args: Vec<Expr<'tcx>>,
    pub conds: Vec<Cond<'tcx>>,
    pub end: End<'tcx>,
}

impl<'tcx> Rule<'tcx> {
    fn from_prerule(
        Prerule {
            init_env,
            conds,
            end,
        }: Prerule<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
        is_main: bool,
        def_request: &mut DefRequest<'tcx>,
    ) -> Self {
        let mut args = init_env
            .into_iter()
            .map(|(_, expr)| expr)
            .collect::<Vec<_>>();
        let res_ty = _0.get_ty(mir_access);
        if !res_ty.is_unit() {
            args.push(Expr::from_var(Var::SelfResult, res_ty));
        }
        if is_main {
            args.push(Expr::from_var(Var::SelfPanic, mir_access.get_bool()));
        }
        let mut vars: IndexMap<Var, Ty> = IndexMap::new();
        args.gather_vars(mir_access, def_request, &mut vars);
        conds.gather_vars(mir_access, def_request, &mut vars);
        end.gather_vars(mir_access, def_request, &mut vars);
        let vars = def_request.update_by_vars(vars, mir_access);
        Rule {
            vars,
            args,
            conds,
            end,
        }
    }
}

#[derive(Debug)]
pub struct PivotDef<'tcx> {
    pub param_tys: Vec<Ty<'tcx>>,
    pub rules: Vec<Rule<'tcx>>,
}
/// A unit corresponding to predicates to be generated.
///
/// We treat the CFG as a full n-ary tree that branches only at `SwitchInt`s, and call these edges `Pivot`s.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pivot {
    Entry,
    /// comes from `SwitchInt` terminator
    Switch(BasicBlock),
}

pub type FunDef<'tcx> = Vec<(Pivot, PivotDef<'tcx>)>;
pub type FunDefRef<'a, 'tcx> = &'a [(Pivot, PivotDef<'tcx>)];

#[derive(Debug, Copy, Clone)]
enum DiscriminantKind {
    Value,
    Tag,
}

#[derive(Copy, Clone)]
struct Data<'a, 'steal, 'tcx> {
    ins_map: &'a IndexMap<BasicBlock, OrderedSet<Local>>,
    outs_map: &'a IndexMap<BasicBlock, OrderedSet<Local>>,
    basic: Basic<'a, 'tcx>,
    mir_access: MirAccess<'steal, 'tcx>,
}
impl<'a, 'tcx> Data<'a, '_, 'tcx> {
    fn get_locals(self, pivot: Pivot) -> &'a OrderedSet<Local> {
        let Data {
            ins_map, outs_map, ..
        } = self;
        if let Pivot::Switch(bb) = pivot {
            &outs_map[&bb]
        } else {
            &ins_map[&BB0]
        }
    }
    fn place_discriminant_kind(self, pivot: BasicBlock) -> (Place<'tcx>, DiscriminantKind) {
        let Data { basic, .. } = self;
        let bbd = &basic[pivot];
        match &bbd.terminator().kind {
            TerminatorKind::SwitchInt { discr, .. } => match bbd.statements.last() {
                Some(Statement {
                    kind: StatementKind::Assign(box (_, Rvalue::Discriminant(place))),
                    ..
                }) => (*place, DiscriminantKind::Tag),
                _ => match discr {
                    Operand::Copy(place) | Operand::Move(place) => {
                        (*place, DiscriminantKind::Value)
                    }
                    Operand::Constant(..) => {
                        panic!("unexpected operand {discr:?} for a discriminant")
                    }
                },
            },
            _ => panic!("unexpected type of pivot for a discriminant"),
        }
    }
    fn get_param_tys(self, is_main: bool, pivot: Pivot) -> Vec<Ty<'tcx>> {
        let Data { mir_access, .. } = self;
        let locals = self.get_locals(pivot).clone();
        let mut res: Vec<_> = locals
            .into_iter()
            .map(|local| local.get_ty(mir_access))
            .collect();
        let res_ty = _0.get_ty(mir_access);
        if !res_ty.is_unit() {
            res.push(res_ty);
        }
        if is_main {
            res.push(mir_access.get_bool());
        }
        res
    }
}

fn pivot_up<'tcx>(
    init_env: Env<'tcx>,
    is_main: bool,
    pivot: BasicBlock,
    mut conds: Vec<Cond<'tcx>>,
    mut env: Env<'tcx>,
    data: Data<'_, '_, 'tcx>,
) -> Prerule<'tcx> {
    let Data { mir_access, .. } = data;
    let mut args = Vec::<Expr<'tcx>>::new();
    for local in data.get_locals(Pivot::Switch(pivot)).clone() {
        args.push(
            env.swap_remove(&local)
                .unwrap_or_else(|| Expr::uninit(local.get_ty(mir_access))),
        );
    }
    for (local, expr) in env {
        expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
    }
    let res_ty = _0.get_ty(mir_access);
    if !res_ty.is_unit() {
        args.push(Expr::from_var(Var::SelfResult, res_ty));
    }
    if is_main {
        args.push(Expr::from_var(Var::SelfPanic, mir_access.get_bool()));
    }
    Prerule {
        init_env,
        conds,
        end: End::Pivot {
            next_switch: pivot,
            args,
        },
    }
}
fn get_prerule<'tcx>(
    is_main: bool,
    init_bb: BasicBlock,
    init_env: Env<'tcx>,
    data: Data<'_, '_, 'tcx>,
    def_request: &mut DefRequest<'tcx>,
) -> Prerule<'tcx> {
    let mut bb = init_bb;
    let mut conds = Vec::<Cond<'tcx>>::new();
    let mut env = init_env.clone();
    let Data {
        basic, mir_access, ..
    } = data;
    loop {
        if let TerminatorKind::Call { target: None, .. } = &basic[bb].terminator().kind {
            for (local, expr) in env {
                expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
            }
            return Prerule {
                init_env,
                conds,
                end: End::Panic,
            };
        }
        for (stmt_index, stmt) in basic[bb].statements.iter().enumerate() {
            gather_conds_from_statement(
                stmt, basic, stmt_index, bb, mir_access, &mut env, &mut conds,
            );
        }
        let terminator = basic[bb].terminator();
        match &terminator.kind {
            TerminatorKind::Goto { target } if *target == bb => {
                return Prerule {
                    init_env,
                    conds,
                    end: End::NeverReturn,
                };
            }
            TerminatorKind::Goto { target }
            | TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. } => {
                bb = *target;
                continue;
            }
            TerminatorKind::Return => {
                let res = env.swap_remove(&_0);
                for (local, expr) in env {
                    expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
                }
                return Prerule {
                    init_env,
                    conds,
                    end: End::Return { res },
                };
            }
            TerminatorKind::SwitchInt { .. } => {
                return pivot_up(init_env, is_main, bb, conds, env, data);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } => {
                let FunTy {
                    def_id,
                    generic_args_ref,
                } = func
                    .get_ty(mir_access)
                    .as_fun_ty()
                    .expect("unexpected/unsupported type for a function");
                let res_ty = destination.get_ty(mir_access);
                let instance = Instance::try_resolve(
                    mir_access.tcx,
                    ParamEnv::reveal_all(),
                    def_id,
                    generic_args_ref,
                )
                .expect("already reported")
                .expect("too generic")
                .polymorphize(mir_access.tcx);
                gather_conds_from_fun(
                    FnCall {
                        instance,
                        args,
                        caller: bb,
                        res_place: destination,
                        res_ty,
                    },
                    mir_access,
                    &mut env,
                    &mut conds,
                    def_request,
                );
                bb = *target;
                continue;
            }
            _ => panic!("unexpected terminator {terminator:?}"),
        }
    }
}

fn gather_conds_from_statement<'tcx>(
    stmt: &Statement<'tcx>,
    basic: Basic,
    stmt_index: usize,
    bb: BasicBlock,
    mir_access: MirAccess<'_, 'tcx>,
    env: &mut Env<'tcx>,
    conds: &mut Vec<Cond<'tcx>>,
) {
    match &stmt.kind {
        StatementKind::Assign(box (_, Rvalue::Discriminant(_))) => {
            assert!(stmt_index == basic[bb].statements.len() - 1);
            let terminator = basic[bb].terminator();
            let TerminatorKind::SwitchInt { .. } = &terminator.kind else {
                panic!("unexpected terminator {terminator:?} for taking discriminant",)
            };
        }
        StatementKind::Assign(box (place, Rvalue::Use(Operand::Copy(mutbor))))
            if mutbor.get_ty(mir_access).ref_mutability() == Some(Mutability::Mut) =>
        {
            let expr = mutbor.get_mut_expr(env, mir_access);
            let ty_body = Ty::new(mutbor.get_ty(mir_access).builtin_deref(false).unwrap());
            if let Expr::Path(path) = expr {
                let ref_ty = mutbor.get_ty(mir_access);
                *expr = Expr::pair(ref_ty, Expr::decompose_mut_path(path));
            }
            let Some((ty, fst, _)) = expr.as_mut_pair() else {
                panic!("unexpected expression {expr:?} for a mutable reference");
            };
            let new_expr = fst.do_borrow_mut(ty_body, ty, (bb, stmt_index));
            place.assign(new_expr, env, conds, mir_access);
        }
        StatementKind::Assign(box (place, rvalue)) => {
            let expr = rvalue.get_expr_at((bb, stmt_index), env, mir_access);
            place.assign(expr, env, conds, mir_access);
        }
        StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => {
            set_tag(place, *variant_index, env, mir_access);
        }
        StatementKind::StorageLive(_)
        | StatementKind::AscribeUserType(_, _)
        | StatementKind::Nop
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..) => {}
        StatementKind::StorageDead(local) => {
            if let Some(expr) = env.swap_remove(local) {
                expr.do_drop(local.get_ty(mir_access), mir_access, conds);
            }
        }
        _ => panic!("unsupported statement {stmt:?}"),
    }
}

struct FnCall<'a, 'tcx> {
    instance: Instance<'tcx>,
    args: &'a [Spanned<Operand<'tcx>>],
    caller: BasicBlock,
    res_place: &'a Place<'tcx>,
    res_ty: Ty<'tcx>,
}

fn gather_conds_from_fun<'tcx>(
    FnCall {
        instance,
        args,
        caller,
        res_place,
        res_ty,
    }: FnCall<'_, 'tcx>,
    mir_access: MirAccess<'_, 'tcx>,
    env: &mut Env<'tcx>,
    conds: &mut Vec<Cond<'tcx>>,
    def_request: &mut DefRequest<'tcx>,
) {
    let did = instance.def_id();
    let fun_name = pr_fun_name(did);
    if let Some(intrinsic) = library::is_intrinsic(mir_access.tcx, did) {
        match intrinsic {
            IntrinsicKind::BinOp(bin_op) => {
                let res = Expr::from_bin_op(
                    bin_op,
                    args[0].node.get_expr(env, mir_access),
                    args[1].node.get_expr(env, mir_access),
                );
                let res = if bin_op.is_overflow_kind() {
                    Expr::pair(res_ty, (res, Expr::Const(Const::Bool(false))))
                } else {
                    res
                };
                res_place.assign(res, env, conds, mir_access);
            }
            IntrinsicKind::UnOp(un_op) => {
                let res = Expr::UnOp(un_op, Box::new(args[0].node.get_expr(env, mir_access)));
                res_place.assign(res, env, conds, mir_access);
            }
        }
    } else if fun_name == "<rand>" {
        let res = Expr::from_var(Var::Rand { caller }, res_ty);
        res_place.assign(res, env, conds, mir_access);
    } else if fun_name == "<swap>" {
        assert!(args.len() == 2);
        let (x, x_) = args[0].node.get_expr(env, mir_access).decompose_mut();
        let (y, y_) = args[1].node.get_expr(env, mir_access).decompose_mut();
        conds.push(Cond::Eq { tgt: y_, src: x });
        conds.push(Cond::Eq { tgt: x_, src: y });
    } else if fun_name == "<free>" {
        // do nothing
    } else {
        def_request.analyze_fun(did);
        let mut args: Vec<_> = args
            .iter()
            .map(|arg| arg.node.get_expr(env, mir_access))
            .collect();
        if !res_ty.is_unit() {
            let res = Expr::from_var(Var::CallResult { caller }, res_ty);
            res_place.assign(res.clone(), env, conds, mir_access);
            args.push(res);
        }
        conds.push(Cond::CallRustFn { fun_id: did, args });
    }
}

fn analyze_pivot<'tcx>(
    is_main: bool,
    pivot: Pivot,
    data: Data<'_, '_, 'tcx>,
    def_request: &mut DefRequest<'tcx>,
) -> PivotDef<'tcx> {
    let Data {
        basic, mir_access, ..
    } = data;
    let mut prerules = Vec::<Prerule<'tcx>>::new();
    let param_tys = data.get_param_tys(is_main, pivot);
    let mut env = Env::from_iter(data.get_locals(pivot).clone().into_iter().map(|local| {
        (
            local,
            Expr::Path(Path::Var(Var::Input { local }, local.get_ty(mir_access))),
        )
    }));
    match pivot {
        Pivot::Entry => {
            prerules.push(get_prerule(is_main, BB0, env, data, def_request));
        }
        Pivot::Switch(bb) => {
            let terminator = &basic[bb].terminator();
            if let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind {
                let (discr_place, discr_kind) = data.place_discriminant_kind(bb);
                let discr_ty = discr_place.get_ty(mir_access);
                let main_targets = targets.iter().collect::<Vec<_>>();
                let rest_target = targets.otherwise();
                match discr_kind {
                    DiscriminantKind::Value => match &discr_ty.kind() {
                        TyKind::Bool => {
                            assert!(main_targets.len() == 1 && main_targets[0].0 == 0);
                            for (b, tgt) in [(false, &main_targets[0].1), (true, &rest_target)] {
                                let mut env = env.clone();
                                *discr_place.get_mut_expr(&mut env, mir_access) =
                                    Expr::Const(Const::Bool(b));
                                prerules.push(get_prerule(is_main, *tgt, env, data, def_request));
                            }
                        }
                        TyKind::Int(_) | TyKind::Uint(_) => {
                            let mut neq_srcs = vec![];
                            for (val, tgt) in &main_targets {
                                let mut env = env.clone();
                                let val_expr = Expr::Const(Const::Int(Int::Uint(*val)));
                                *discr_place.get_mut_expr(&mut env, mir_access) = val_expr.clone();
                                prerules.push(get_prerule(is_main, *tgt, env, data, def_request));
                                neq_srcs.push(val_expr);
                            }
                            let neq_tgt = discr_place.get_expr(&mut env, mir_access);
                            let mut prerule =
                                get_prerule(is_main, rest_target, env, data, def_request);
                            prerule.conds.push(Cond::Neq {
                                tgt: neq_tgt,
                                srcs: neq_srcs,
                            });
                            prerules.push(prerule);
                        }
                        _ => unimplemented!("unsupported branching"),
                    },
                    DiscriminantKind::Tag => match discr_ty.kind() {
                        TyKind::Adt(adt_def, adt_substs) => {
                            let variants = adt_def.variants();
                            assert!(variants.len() == main_targets.len());
                            for ((variant_index, VariantDef { fields, .. }), (val, tgt)) in
                                variants.iter_enumerated().zip(main_targets.iter())
                            {
                                assert!(*val == u128::from(variant_index.as_u32()));
                                let mut env = env.clone();
                                let args = fields
                                    .iter_enumerated()
                                    .map(|(field_index, fld_def): (FieldIdx, &FieldDef)| {
                                        Expr::from_var(
                                            Var::Split(bb, variant_index, field_index),
                                            fld_def.get_ty_with(mir_access, adt_substs),
                                        )
                                    })
                                    .collect::<Vec<_>>();
                                *discr_place.get_mut_expr(&mut env, mir_access) = Expr::Aggregate {
                                    ty: discr_ty,
                                    variant_index,
                                    fields: args,
                                };
                                prerules.push(get_prerule(is_main, *tgt, env, data, def_request));
                            }
                        }
                        _ => panic!("unexpected tag branching for a non-adt type {discr_ty:?}"),
                    },
                }
            } else {
                panic!("unexpected terminator {terminator:?} for a pivot");
            }
        }
    }
    let rules = prerules
        .into_iter()
        .map(|prerule| Rule::from_prerule(prerule, mir_access, is_main, def_request))
        .collect();
    PivotDef { param_tys, rules }
}

fn analyze_fun<'tcx>(
    fun_id: DefId,
    tcx: TyCtxt<'tcx>,
    def_request: &mut DefRequest<'tcx>,
) -> FunDef<'tcx> {
    let mir = tcx.mir_built(fun_id.expect_local()).borrow();
    let bbds = &mir.basic_blocks;
    let mir_access = MirAccess { mir: &mir, tcx };
    /* preparations */
    let basic = Basic { bbds };
    let (ins_map, outs_map) = basic.get_ins_outs_map(mir.arg_count);
    let data = Data {
        ins_map: &ins_map,
        outs_map: &outs_map,
        basic,
        mir_access,
    };
    /* wrap up */
    let mut fun_def = IndexMap::<Pivot, PivotDef<'tcx>>::new();
    let is_main = is_main(tcx, fun_id);
    for pivot in
        std::iter::once(Pivot::Entry).chain(basic.get_switches().into_iter().map(Pivot::Switch))
    {
        fun_def.insert(pivot, analyze_pivot(is_main, pivot, data, def_request));
    }
    fun_def.into_iter().collect()
}

/// Definitions of functions and sorts.
pub struct Summary<'tcx> {
    pub fun_defs: Vec<(DefId, FunDef<'tcx>)>,
    pub adt_ids: Vec<DefId>,
    pub tuples: Vec<Tys<'tcx>>,
    pub mut_tuples: Vec<Ty<'tcx>>,
}

pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>) -> Summary<'tcx> {
    let mut fun_defs: IndexMap<DefId, FunDef<'tcx>> = IndexMap::new();
    let mut def_request = DefRequest::default();
    /* analyze the main function */
    let Some((main, EntryFnType::Main { .. })) = tcx.entry_fn(()) else {
        panic!("no main function!");
    };
    fun_defs.insert(main, analyze_fun(main, tcx, &mut def_request));

    /* analyze required functions */
    loop {
        let requested_funs: Vec<_> = def_request.accept_analyze_fun().collect();
        if requested_funs.is_empty() {
            break;
        }
        for fun_id in requested_funs {
            fun_defs
                .entry(fun_id)
                .or_insert_with(|| analyze_fun(fun_id, tcx, &mut def_request));
        }
    }
    /* return results */
    let DefRequest {
        fun_ids,
        adt_ids,
        tuples,
        mut_tuples,
    } = def_request;
    assert!(fun_ids.is_empty());
    Summary {
        fun_defs: fun_defs.into_iter().collect(),
        adt_ids: adt_ids.into_iter().collect(),
        tuples: tuples.into_iter().collect(),
        mut_tuples: mut_tuples.into_iter().collect(),
    }
}

#[derive(Debug, Default)]
/// Request for a definition.
pub struct DefRequest<'tcx> {
    fun_ids: IndexSet<DefId>,
    adt_ids: IndexSet<DefId>,
    tuples: IndexSet<Tys<'tcx>>,
    mut_tuples: IndexSet<Ty<'tcx>>,
}

impl<'tcx> DefRequest<'tcx> {
    pub fn analyze_fun(&mut self, fun_ty: DefId) { self.fun_ids.insert(fun_ty); }
    pub fn add_adt_def(&mut self, def_id: DefId) -> bool { self.adt_ids.insert(def_id) }
    pub fn add_tuple_def(&mut self, tys: Tys<'tcx>) -> bool { self.tuples.insert(tys) }
    pub fn add_mut_tuple_def(&mut self, ty: Ty<'tcx>) -> bool { self.mut_tuples.insert(ty) }
    /// Accept the request for analyzing a function. Returns an iterator of the requested functions.
    pub fn accept_analyze_fun(&mut self) -> impl Iterator<Item = DefId> {
        std::mem::take(&mut self.fun_ids).into_iter()
    }
}

pub trait GatherVars<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'_, 'tcx>,
        def_request: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    );
}

fn traverse_path<'tcx>(path: &Path<'tcx>, vars: &mut IndexMap<Var, Ty<'tcx>>) {
    match path {
        Path::Var(var, ty) => {
            vars.insert(*var, *ty);
        }
        Path::Proj { body: path, .. } => traverse_path(path, vars),
    }
}

impl<'tcx> GatherVars<'tcx> for Path<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'_, 'tcx>,
        _: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        traverse_path(self, vars);
    }
}

impl<'tcx> GatherVars<'tcx> for Expr<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'_, 'tcx>,
        _: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        fn traverse_expr<'tcx>(expr: &Expr<'tcx>, vars: &mut IndexMap<Var, Ty<'tcx>>) {
            match expr {
                Expr::Path(path) => {
                    traverse_path(path, vars);
                }
                Expr::Const(_) => {}
                Expr::BinOp(_, expr1, expr2) => {
                    traverse_expr(expr1, vars);
                    traverse_expr(expr2, vars);
                }
                Expr::UnOp(_, expr) => {
                    traverse_expr(expr, vars);
                }
                Expr::Aggregate { fields, .. } => {
                    for field in fields {
                        traverse_expr(field, vars);
                    }
                }
                Expr::Construct { name: _, args } => {
                    for arg in args {
                        traverse_expr(arg, vars);
                    }
                }
            }
        }

        traverse_expr(self, vars);
    }
}

impl<'tcx> GatherVars<'tcx> for Cond<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'_, 'tcx>,
        def_request: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        match self {
            Cond::Drop { arg, .. } => {
                arg.gather_vars(mir_access, def_request, vars);
            }
            Cond::Eq { tgt, src } => {
                tgt.gather_vars(mir_access, def_request, vars);
                src.gather_vars(mir_access, def_request, vars);
            }
            Cond::Neq { tgt, srcs } => {
                tgt.gather_vars(mir_access, def_request, vars);
                srcs.gather_vars(mir_access, def_request, vars);
            }
            Cond::CallRustFn { args, .. } | Cond::Intrinsic { args, .. } => {
                args.gather_vars(mir_access, def_request, vars);
            }
        }
    }
}

impl<'tcx> GatherVars<'tcx> for End<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'_, 'tcx>,
        def_request: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        match self {
            End::Pivot { args, .. } => {
                args.gather_vars(mir_access, def_request, vars);
            }
            End::Return { res } => {
                if let Some(expr) = res {
                    expr.gather_vars(mir_access, def_request, vars);
                }
            }
            End::Panic | End::NeverReturn => {}
        };
    }
}

impl<'tcx, T: GatherVars<'tcx>> GatherVars<'tcx> for Vec<T> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'_, 'tcx>,
        def_request: &mut DefRequest<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        for item in self {
            item.gather_vars(mir_access, def_request, vars);
        }
    }
}

impl<'tcx> DefRequest<'tcx> {
    fn update_by_ty(&mut self, ty: Ty<'tcx>, mir_access: MirAccess<'_, 'tcx>) {
        match ty.kind() {
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {}
            TyKind::Adt(adt_def, adt_substs) => {
                if adt_def.is_box() {
                    for ty in adt_substs.types() {
                        self.update_by_ty(Ty::new(ty), mir_access);
                    }
                } else if library::need_to_rename_ty(mir_access.tcx, adt_def.did()).is_some() {
                    // do nothing
                } else if self.add_adt_def(adt_def.did()) {
                    for fld_def in adt_def.all_fields() {
                        self.update_by_ty(fld_def.get_ty_with(mir_access, adt_substs), mir_access);
                    }
                }
            }
            TyKind::Ref(_, ty, mutability) => {
                let ty = Ty::new(*ty);
                if let Mutability::Mut = mutability {
                    self.add_mut_tuple_def(ty);
                }
                self.update_by_ty(ty, mir_access);
            }
            TyKind::Tuple(types) => {
                self.add_tuple_def(types);
                for ty in types.into_iter() {
                    let ty = Ty::new(ty);
                    self.update_by_ty(ty, mir_access);
                }
            }
            _ => panic!("unsupported type {ty}"),
        }
    }

    pub fn update_by_vars(
        &mut self,
        vars: IndexMap<Var, Ty<'tcx>>,
        mir_access: MirAccess<'_, 'tcx>,
    ) -> Vec<(Var, Ty<'tcx>)> {
        for (_, ty) in &vars {
            self.update_by_ty(*ty, mir_access);
        }
        vars.into_iter().collect()
    }
}
