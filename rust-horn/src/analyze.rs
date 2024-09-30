use std::collections::HashMap;

use crate::library::intrinsic::{is_intrinsic, IntrinsicKind};
use crate::prettify::pr_fun_name;
use crate::represent::rep_fun_name;
use crate::types::{
    BasicBlock, DefId, EntryFnType, FieldDef, FieldIdx, FunTy, Instance, Local, Map, Mutability,
    Operand, OrderedSet, ParamEnv, Place, Rvalue, Set, Spanned, Statement, StatementKind,
    TerminatorKind, Ty, TyCtxt, TyKind, Tys, VariantDef,
};
use crate::util::{BB0, VRT0, _0};

pub mod graph;
use graph::Basic;

pub mod data;
use data::{
    set_tag, AssignExt, BasicAsks, Cond, Const, DropExt, End, Env, Expr, GetTypeExt, Int,
    MirAccess, MirAccessCtxExt, Path, ReadExprCtxExt, ReadExprExt, ReadExprMutExt, Var,
};

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
        Prerule { init_env, conds, end }: Prerule<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
        is_main: bool,
        basic_asks: &mut BasicAsks<'tcx>,
    ) -> Self {
        use data::GatherVars;
        let mut args = init_env.into_iter().map(|(_, expr)| expr).collect::<Vec<_>>();
        let res_ty = _0.get_ty(mir_access);
        if !res_ty.is_unit() {
            args.push(Expr::from_var(Var::SelfResult, res_ty));
        }
        if is_main {
            args.push(Expr::from_var(Var::SelfPanic, mir_access.get_bool()));
        }
        let mut vars: Map<Var, Ty> = Map::new();
        args.gather_vars(mir_access, basic_asks, &mut vars);
        conds.gather_vars(mir_access, basic_asks, &mut vars);
        end.gather_vars(mir_access, basic_asks, &mut vars);
        let vars = basic_asks.update_by_vars(vars, mir_access);
        Rule { vars, args, conds, end }
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
    /// comes from SwitchInt terminator
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
    ins_map: &'a Map<BasicBlock, OrderedSet<Local>>,
    outs_map: &'a Map<BasicBlock, OrderedSet<Local>>,
    basic: Basic<'a, 'tcx>,
    mir_access: MirAccess<'steal, 'tcx>,
}
impl<'a, 'tcx> Data<'a, '_, 'tcx> {
    fn get_locals(self, pivot: Pivot) -> &'a OrderedSet<Local> {
        let Data { ins_map, outs_map, .. } = self;
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
                        panic!("unexpected operand {:?} for a discriminant", discr)
                    }
                },
            },
            _ => panic!("unexpected type of pivot for a discriminant"),
        }
    }
    fn get_param_tys(self, is_main: bool, pivot: Pivot) -> Vec<Ty<'tcx>> {
        let Data { mir_access, .. } = self;
        let locals = self.get_locals(pivot).clone();
        let mut res: Vec<_> = locals.into_iter().map(|local| local.get_ty(mir_access)).collect();
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
        args.push(env.remove(&local).unwrap_or_else(|| Expr::uninit(local.get_ty(mir_access))));
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
    Prerule { init_env, conds, end: End::Pivot { next_switch: pivot, args } }
}
fn get_prerule<'tcx>(
    is_main: bool,
    init_bb: BasicBlock,
    init_env: Env<'tcx>,
    data: Data<'_, '_, 'tcx>,
    fun_asks: &mut Map<String, FunTy<'tcx>>,
) -> Prerule<'tcx> {
    let mut bb = init_bb;
    let mut conds = Vec::<Cond<'tcx>>::new();
    let mut env = init_env.clone();
    let Data { basic, mir_access, .. } = data;
    loop {
        if let TerminatorKind::Call { target: None, .. } = &&basic[bb].terminator().kind {
            for (local, expr) in env {
                dbg!(&local, &expr);
                expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
            }
            return Prerule { init_env, conds, end: End::Panic };
        }
        for (stmt_index, stmt) in basic[bb].statements.iter().enumerate() {
            gather_conds_from_statement(
                stmt, basic, stmt_index, bb, mir_access, &mut env, &mut conds,
            );
        }
        let terminator = &basic[bb].terminator();
        match &terminator.kind {
            TerminatorKind::Goto { target } if *target == bb => {
                return Prerule { init_env, conds, end: End::NeverReturn };
            }
            TerminatorKind::Goto { target }
            | TerminatorKind::FalseEdge { real_target: target, .. }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. } => {
                bb = *target;
                continue;
            }
            TerminatorKind::Return => {
                let res = env.remove(&_0);
                for (local, expr) in env {
                    expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
                }
                return Prerule { init_env, conds, end: End::Return { res } };
            }
            TerminatorKind::SwitchInt { .. } => {
                return pivot_up(init_env, is_main, bb, conds, env, data);
            }
            TerminatorKind::Call { func, args, destination, target: Some(target), .. } => {
                let fun_ty @ FunTy { def_id, generic_args_ref } = func
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
                        ty: fun_ty,
                        instance,
                        args,
                        caller: bb,
                        res_place: destination,
                        res_ty,
                    },
                    mir_access,
                    &mut env,
                    &mut conds,
                    fun_asks,
                );
                bb = *target;
                continue;
            }
            _ => panic!("unexpected terminator {:?}", terminator),
        }
    }
}

fn gather_conds_from_statement<'tcx>(
    stmt: &Statement<'tcx>,
    basic: Basic,
    stmt_index: usize,
    bb: BasicBlock,
    mir_access: MirAccess<'_, 'tcx>,
    env: &mut Map<Local, Expr<'tcx>>,
    conds: &mut Vec<Cond<'tcx>>,
) {
    dbg!(stmt);
    match &stmt.kind {
        StatementKind::Assign(box (_, Rvalue::Discriminant(_))) => {
            assert!(stmt_index == basic[bb].statements.len() - 1);
            let terminator = &basic[bb].terminator();
            match &terminator.kind {
                TerminatorKind::SwitchInt { .. } => {}
                _ => panic!("unexpected terminator {:?} for taking discriminant", terminator),
            }
        }
        StatementKind::Assign(box (place, Rvalue::Use(Operand::Copy(mutbor))))
            if mutbor.get_ty(mir_access).is_mutable_ptr() =>
        {
            let expr = mutbor.get_mut_expr(env, mir_access);
            let ty_body = match mutbor.get_ty(mir_access).kind() {
                TyKind::Ref(_, ty_body, Mutability::Mut) => ty_body,
                _ => unreachable!(),
            };
            let ty_body = Ty::new(*ty_body);
            if let Expr::Path(path) = expr {
                let ref_ty = mutbor.get_ty(mir_access);
                *expr = Expr::pair(ref_ty, Expr::decompose_mut_path(path));
            }
            match expr {
                Expr::Aggregate { ty, variant_index: VRT0, fields } => {
                    assert!(fields.len() == 2);
                    let new_expr = fields[0].do_borrow_mut(ty_body, *ty, (bb, stmt_index));
                    place.assign(new_expr, env, conds, mir_access);
                }
                _ => panic!("unexpected expression {:?} for a mutable reference", expr),
            }
        }
        StatementKind::Assign(box (place, rvalue)) => {
            let expr = rvalue.get_expr_at((bb, stmt_index), env, mir_access);
            place.assign(expr, env, conds, mir_access);
        }
        StatementKind::SetDiscriminant { place, variant_index } => {
            set_tag(place, *variant_index, env, mir_access);
        }
        StatementKind::StorageLive(_)
        | StatementKind::AscribeUserType(_, _)
        | StatementKind::Nop
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..) => {}
        StatementKind::StorageDead(local) => {
            if let Some(expr) = env.remove(local) {
                expr.do_drop(local.get_ty(mir_access), mir_access, conds);
            }
        }
        _ => panic!("unsupported statement {:?}", stmt),
    }
}

struct FnCall<'a, 'tcx> {
    ty: FunTy<'tcx>,
    instance: Instance<'tcx>,
    args: &'a [Spanned<Operand<'tcx>>],
    caller: BasicBlock,
    res_place: &'a Place<'tcx>,
    res_ty: Ty<'tcx>,
}

fn gather_conds_from_fun<'tcx>(
    FnCall { ty, instance, args, caller, res_place, res_ty }: FnCall<'_, 'tcx>,
    mir_access: MirAccess<'_, 'tcx>,
    env: &mut Map<Local, Expr<'tcx>>,
    conds: &mut Vec<Cond<'tcx>>,
    fun_asks: &mut Map<String, FunTy<'tcx>>,
) {
    let did = instance.def_id();
    let fun_name = pr_fun_name(did);
    if let Some(intrinsic) = is_intrinsic(mir_access.tcx, did) {
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
        fun_asks.insert(rep_fun_name(ty), ty);
        let mut args: Vec<_> = args.iter().map(|arg| arg.node.get_expr(env, mir_access)).collect();
        if !res_ty.is_unit() {
            let res = Expr::from_var(Var::CallResult { caller }, res_ty);
            res_place.assign(res.clone(), env, conds, mir_access);
            args.push(res.clone());
        }
        conds.push(Cond::Call { fun_ty: ty, args });
    }
}

fn analyze_pivot<'tcx>(
    is_main: bool,
    pivot: Pivot,
    data: Data<'_, '_, 'tcx>,
    basic_asks: &mut BasicAsks<'tcx>,
) -> PivotDef<'tcx> {
    let Data { basic, mir_access, .. } = data;
    let BasicAsks { fun_asks, .. } = basic_asks;
    let mut prerules = Vec::<Prerule<'tcx>>::new();
    let param_tys = data.get_param_tys(is_main, pivot);
    let env = data
        .get_locals(pivot)
        .clone()
        .into_iter()
        .map(|local| (local, Expr::Path(Path::Var(Var::Input { local }, local.get_ty(mir_access)))))
        .collect::<HashMap<_, _>>();
    let mut env = Env::from_inner(env);
    match pivot {
        Pivot::Entry => {
            prerules.push(get_prerule(is_main, BB0, env.clone(), data, fun_asks));
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
                                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
                            }
                        }
                        TyKind::Int(_) | TyKind::Uint(_) => {
                            let mut neq_srcs = vec![];
                            for (val, tgt) in &main_targets {
                                let mut env = env.clone();
                                let val_expr = Expr::Const(Const::Int(Int::Uint(*val)));
                                *discr_place.get_mut_expr(&mut env, mir_access) = val_expr.clone();
                                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
                                neq_srcs.push(val_expr);
                            }
                            let neq_tgt = discr_place.get_expr(&mut env, mir_access);
                            let mut prerule =
                                get_prerule(is_main, rest_target, env, data, fun_asks);
                            prerule.conds.push(Cond::Neq { tgt: neq_tgt, srcs: neq_srcs });
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
                                    .iter()
                                    .enumerate()
                                    .map(|(field_index, fld_def): (usize, &FieldDef)| {
                                        Expr::from_var(
                                            Var::Split(
                                                bb,
                                                variant_index,
                                                FieldIdx::from(field_index),
                                            ),
                                            fld_def.get_ty_with(mir_access, adt_substs),
                                        )
                                    })
                                    .collect::<Vec<_>>();
                                *discr_place.get_mut_expr(&mut env, mir_access) =
                                    Expr::Aggregate { ty: discr_ty, variant_index, fields: args };
                                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
                            }
                        }
                        _ => panic!("unexpected tag branching for a non-adt type {:?}", discr_ty),
                    },
                }
            } else {
                panic!("unexpected terminator {:?} for a pivot", terminator);
            }
        }
    }
    let rules = prerules
        .into_iter()
        .map(|prerule| Rule::from_prerule(prerule, mir_access, is_main, basic_asks))
        .collect();
    PivotDef { param_tys, rules }
}

fn analyze_fun<'tcx>(
    fun_ty: FunTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    basic_asks: &mut BasicAsks<'tcx>,
) -> FunDef<'tcx> {
    let mir = tcx.mir_built(fun_ty.def_id.expect_local()).borrow();
    let bbds = &mir.basic_blocks;
    let mir_access = MirAccess { mir: &mir, generic_args: fun_ty.generic_args_ref, tcx };
    /* preparations */
    let basic = Basic { bbds };
    let (ins_map, outs_map) = basic.get_ins_outs_map(mir.arg_count);
    let data = Data { ins_map: &ins_map, outs_map: &outs_map, basic, mir_access };
    /* wrap up */
    let mut fun_def = Map::<Pivot, PivotDef<'tcx>>::new();
    let is_main = &rep_fun_name(fun_ty) == "%main";
    for pivot in
        std::iter::once(Pivot::Entry).chain(basic.get_switches().into_iter().map(Pivot::Switch))
    {
        fun_def.insert(pivot, analyze_pivot(is_main, pivot, data, basic_asks));
    }
    fun_def.into_sorted_vec()
}

pub struct Summary<'tcx> {
    pub fun_defs: Vec<(String, FunDef<'tcx>)>,
    pub drop_defs: Vec<(String, FunDef<'tcx>)>,
    pub adt_asks: Vec<DefId>,
    pub tup_asks: Vec<(String, Tys<'tcx>)>,
    pub mut_asks: Vec<(String, Ty<'tcx>)>,
}

fn get_drop_def<'tcx>(
    _ty: Ty<'tcx>,
    _tcx: TyCtxt<'tcx>,
    _basic_asks: &mut BasicAsks<'tcx>,
) -> FunDef<'tcx> {
    unimplemented!();
}

pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>) -> Summary<'tcx> {
    let mut fun_defs: Map<String, FunDef<'tcx>> = Map::new();
    let mut basic_asks = BasicAsks {
        fun_asks: Map::new(),
        drop_asks: Map::new(),
        adt_asks: Set::new(),
        tup_asks: Map::new(),
        mut_asks: Map::new(),
    };
    /* analyze the main function */
    if let Some((main, EntryFnType::Main { .. })) = tcx.entry_fn(()) {
        let main_ty = tcx.type_of(main);
        let main_ty = Ty::new(main_ty.skip_binder())
            .as_fun_ty()
            .expect("unexpected/unsupported type for a function");
        let main_name = rep_fun_name(main_ty);
        fun_defs.insert(main_name, analyze_fun(main_ty, tcx, &mut basic_asks));
    } else {
        panic!("no main function!");
    }
    /* analyze required functions */
    loop {
        let fun_asks = std::mem::take(&mut basic_asks.fun_asks).into_sorted_vec();
        if fun_asks.is_empty() {
            break;
        }
        for (fun_name, fun_ty) in fun_asks {
            fun_defs.entry(fun_name).or_insert_with(|| analyze_fun(fun_ty, tcx, &mut basic_asks));
        }
    }
    /* added drop functions */
    let mut drop_defs: Map<String, FunDef<'tcx>> = Map::new();
    for (drop_name, ty) in std::mem::take(&mut basic_asks.drop_asks).drain() {
        drop_defs.entry(drop_name).or_insert_with(|| get_drop_def(ty, tcx, &mut basic_asks));
    }
    /* return results */
    let BasicAsks { fun_asks, drop_asks, adt_asks, tup_asks, mut_asks } = basic_asks;
    assert!(fun_asks.is_empty() && drop_asks.is_empty());
    Summary {
        fun_defs: fun_defs.into_sorted_vec(),
        drop_defs: drop_defs.into_sorted_vec(),
        adt_asks: adt_asks.into_inner_vec(),
        tup_asks: tup_asks.into_sorted_vec(),
        mut_asks: mut_asks.into_sorted_vec(),
    }
}
