use crate::library::{self, IntrinsicKind};
use crate::prettify::pr_fun_name;
use crate::types::{
    BasicBlock, DefId, EntryFnType, FieldDef, FieldIdx, FunTy, Instance, Local, Operand,
    OrderedSet, ParamEnv, Place, RhTyKind, Rvalue, Spanned, Statement, StatementKind,
    TerminatorKind, Ty, TyCtxt, Tys, VariantDef,
};
use crate::util::{is_main, RETURN_PLACE, START_BLOCK};

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
        def_request: &mut Request<'tcx>,
    ) -> Self {
        let mut args = init_env
            .into_iter()
            .map(|(_, expr)| expr)
            .collect::<Vec<_>>();
        finalize_args(&mut args, mir_access, is_main);
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

fn finalize_args<'tcx>(args: &mut Vec<Expr<'tcx>>, mir_access: MirAccess<'_, 'tcx>, is_main: bool) {
    let res_ty = RETURN_PLACE.get_ty(mir_access);
    if !res_ty.is_unit() {
        args.push(Expr::from_var(Var::SelfResult, res_ty));
    }
    if is_main {
        args.push(Expr::from_var(Var::SelfPanic, mir_access.bool()));
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
            &ins_map[&START_BLOCK]
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
        let res_ty = RETURN_PLACE.get_ty(mir_access);
        if !res_ty.is_unit() {
            res.push(res_ty);
        }
        if is_main {
            res.push(mir_access.bool());
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
        expr.do_drop(&local.get_ty(mir_access), mir_access, &mut conds);
    }
    finalize_args(&mut args, mir_access, is_main);
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
    def_request: &mut Request<'tcx>,
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
                expr.do_drop(&local.get_ty(mir_access), mir_access, &mut conds);
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
                let res = env.swap_remove(&RETURN_PLACE);
                for (local, expr) in env {
                    expr.do_drop(&local.get_ty(mir_access), mir_access, &mut conds);
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
                expr.do_drop(&local.get_ty(mir_access), mir_access, conds);
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
    def_request: &mut Request<'tcx>,
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
    def_request: &mut Request<'tcx>,
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
            prerules.push(get_prerule(is_main, START_BLOCK, env, data, def_request));
        }
        Pivot::Switch(bb) => {
            let terminator = &basic[bb].terminator();
            if let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind {
                let (discr_place, discr_kind) = data.place_discriminant_kind(bb);
                let discriminant_ty = discr_place.get_ty(mir_access);
                let main_targets = targets.iter().collect::<Vec<_>>();
                let rest_target = targets.otherwise();
                match discr_kind {
                    DiscriminantKind::Value => match discriminant_ty.kind() {
                        RhTyKind::Bool => {
                            assert!(main_targets.len() == 1 && main_targets[0].0 == 0);
                            for (b, tgt) in [(false, &main_targets[0].1), (true, &rest_target)] {
                                let mut env = env.clone();
                                *discr_place.get_mut_expr(&mut env, mir_access) =
                                    Expr::Const(Const::Bool(b));
                                prerules.push(get_prerule(is_main, *tgt, env, data, def_request));
                            }
                        }
                        RhTyKind::Int => {
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
                    DiscriminantKind::Tag => {
                        let RhTyKind::Adt { def, args } = discriminant_ty.kind() else {
                            panic!(
                                "unexpected tag branching for a non-adt type {discriminant_ty:?}"
                            )
                        };

                        let variants = def.variants();
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
                                        fld_def.get_ty_with(mir_access, args),
                                    )
                                })
                                .collect::<Vec<_>>();
                            *discr_place.get_mut_expr(&mut env, mir_access) = Expr::Aggregate {
                                ty: discriminant_ty.clone(),
                                variant_index,
                                fields: args,
                            };
                            prerules.push(get_prerule(is_main, *tgt, env, data, def_request));
                        }
                    }
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
    def_request: &mut Request<'tcx>,
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

/// Analyze functions reachable from the main function.
pub fn analyze_from_main_fn<'tcx>(tcx: TyCtxt<'tcx>) -> Summary<'tcx> {
    let mut fun_defs: IndexMap<DefId, FunDef<'tcx>> = IndexMap::new();
    let mut request = Request::default();

    let Some((main, EntryFnType::Main { .. })) = tcx.entry_fn(()) else {
        panic!("there is no entry point; Rust-Horn only works on programs with main function");
    };
    request.analyze_fun(main);

    /* analyze required functions */
    loop {
        let requested_funs: Vec<_> = request.accept_analyze_fun().collect();
        if requested_funs.is_empty() {
            break;
        }
        for fun_id in requested_funs {
            fun_defs
                .entry(fun_id)
                .or_insert_with(|| analyze_fun(fun_id, tcx, &mut request));
        }
    }

    /* return results */
    let Request {
        to_be_analyzed_fun_ids: fun_ids,
        adt_ids,
        tuples,
        tuple_of_muts: mut_tuples,
    } = request;
    assert!(fun_ids.is_empty());
    Summary {
        fun_defs: fun_defs.into_iter().collect(),
        adt_ids: adt_ids.into_iter().collect(),
        tuples: tuples.into_iter().collect(),
        mut_tuples: mut_tuples.into_iter().collect(),
    }
}

#[derive(Debug, Default)]
/// Request for analysis or definition.
pub struct Request<'tcx> {
    to_be_analyzed_fun_ids: IndexSet<DefId>,
    adt_ids: IndexSet<DefId>,
    tuples: IndexSet<Tys<'tcx>>,
    tuple_of_muts: IndexSet<Ty<'tcx>>,
}

impl<'tcx> Request<'tcx> {
    pub fn analyze_fun(&mut self, fun_ty: DefId) { self.to_be_analyzed_fun_ids.insert(fun_ty); }
    pub fn add_adt_def(&mut self, def_id: DefId) -> bool { self.adt_ids.insert(def_id) }
    pub fn add_tuple_def(&mut self, tys: Tys<'tcx>) -> bool { self.tuples.insert(tys) }
    pub fn add_mut_tuple_def(&mut self, ty: Ty<'tcx>) -> bool { self.tuple_of_muts.insert(ty) }

    /// Accept the request for analyzing functions. Returns an iterator of the requested functions.
    pub fn accept_analyze_fun(&mut self) -> impl ExactSizeIterator<Item = DefId> {
        std::mem::take(&mut self.to_be_analyzed_fun_ids).into_iter()
    }
}

pub trait GatherVars<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'_, 'tcx>,
        def_request: &mut Request<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    );
}

fn traverse_path<'tcx>(path: &Path<'tcx>, vars: &mut IndexMap<Var, Ty<'tcx>>) {
    match path {
        Path::Var(var, ty) => {
            vars.insert(*var, ty.clone());
        }
        Path::Proj { body: path, .. } => traverse_path(path, vars),
    }
}

impl<'tcx> GatherVars<'tcx> for Path<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'_, 'tcx>,
        _: &mut Request<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        traverse_path(self, vars);
    }
}

impl<'tcx> GatherVars<'tcx> for Expr<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'_, 'tcx>,
        _: &mut Request<'tcx>,
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
        def_request: &mut Request<'tcx>,
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
        def_request: &mut Request<'tcx>,
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
        def_request: &mut Request<'tcx>,
        vars: &mut IndexMap<Var, Ty<'tcx>>,
    ) {
        for item in self {
            item.gather_vars(mir_access, def_request, vars);
        }
    }
}

impl<'tcx> Request<'tcx> {
    fn update_by_ty(&mut self, ty: &Ty<'tcx>, mir_access: MirAccess<'_, 'tcx>) {
        match ty.kind() {
            RhTyKind::Bool | RhTyKind::Int | RhTyKind::Float => {}
            RhTyKind::Adt { def, args } => {
                if library::need_to_rename_ty(mir_access.tcx, def.did()).is_some() {
                    // do nothing
                } else if self.add_adt_def(def.did()) {
                    for fld_def in def.all_fields() {
                        self.update_by_ty(&fld_def.get_ty_with(mir_access, args), mir_access);
                    }
                }
            }
            RhTyKind::Transparent { box ty, .. } => {
                self.update_by_ty(ty, mir_access);
            }
            RhTyKind::RefMut { box ty } => {
                self.add_mut_tuple_def(ty.clone());
                self.update_by_ty(ty, mir_access);
            }
            RhTyKind::Tuple { elems } => {
                self.add_tuple_def(elems.clone());
                for ty in elems {
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
            self.update_by_ty(ty, mir_access);
        }
        vars.into_iter().collect()
    }
}
