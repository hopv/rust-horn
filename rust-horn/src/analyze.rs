use std::collections::HashMap;

use crate::prettify::pr_fun_name;
use crate::represent::rep_fun_name;
use crate::types::{
    AdtDef, BasicBlock, DefId, EntryFnType, FieldDef, FieldIdx, GenericArgsRef, Local, Map,
    Mutability, Operand, Place, Rvalue, Set, Statement, StatementKind, TerminatorKind, Ty, TyCtxt,
    TyKind, VariantDef,
};
use crate::util::{get_terminator, BB0, VRT0, _0};

pub mod graph;
use graph::{get_ghosts, Basic};

pub mod data;
use data::{
    set_tag, AssignExt, BasicAsks, BinOp, Cond, Const, DropExt, End, Env, Expr, GetTypeExt,
    MirAccess, MirAccessCtxExt, Path, ReadExprCtxExt, ReadExprExt, ReadExprMutExt, UnOp, Var,
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
        mir_access: MirAccess<'tcx>,
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
struct Data<'a, 'tcx> {
    ins_map: &'a Map<BasicBlock, Set<Local>>,
    outs_map: &'a Map<BasicBlock, Set<Local>>,
    basic: Basic<'a, 'tcx>,
    mir_access: MirAccess<'tcx>,
}
impl<'a, 'tcx> Data<'a, 'tcx> {
    fn get_locals(self, pivot: Pivot) -> &'a Set<Local> {
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
        match &get_terminator(bbd).kind {
            TerminatorKind::SwitchInt { discr, .. } if !basic.is_ghost_switching(pivot) => {
                match bbd.statements.last() {
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
                }
            }
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
    data: Data<'_, 'tcx>,
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
    data: Data<'_, 'tcx>,
    fun_asks: &mut Map<String, Ty<'tcx>>,
) -> Prerule<'tcx> {
    let mut bb = init_bb;
    let mut conds = Vec::<Cond<'tcx>>::new();
    let mut env = init_env.clone();
    let Data { basic, mir_access, .. } = data;
    loop {
        if let TerminatorKind::Call { destination: None, .. } = &get_terminator(&basic[bb]).kind {
            for (local, expr) in env {
                expr.do_drop(local.get_ty(mir_access), mir_access, &mut conds);
            }
            return Prerule { init_env, conds, end: End::Panic };
        }
        for (stmt_index, stmt) in basic[bb].statements.iter().enumerate() {
            gather_conds_from_statement(
                stmt, basic, stmt_index, bb, mir_access, &mut env, &mut conds,
            );
        }
        let terminator = get_terminator(&basic[bb]);
        match &terminator.kind {
            TerminatorKind::Goto { target } if *target == bb => {
                return Prerule { init_env, conds, end: End::NeverReturn };
            }
            TerminatorKind::Goto { target }
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
            TerminatorKind::SwitchInt { targets, .. } => {
                if basic.is_ghost_switching(bb) {
                    bb = targets.all_targets()[0];
                    continue;
                }
                return pivot_up(init_env, is_main, bb, conds, env, data);
            }
            TerminatorKind::Call { func, args, destination: Some((place, target)), .. } => {
                let fun_ty = func.get_ty(mir_access);
                let fun = fun_ty.fun_of_fun_ty();
                let fun_name = pr_fun_name(fun);
                let res_ty = place.get_ty(mir_access);
                gather_conds_from_fun(
                    FnCall {
                        ty: fun_ty,
                        did: fun,
                        fun_name,
                        args,
                        caller: bb,
                        res_place: place,
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
    mir_access: MirAccess<'tcx>,
    env: &mut Map<Local, Expr<'tcx>>,
    conds: &mut Vec<Cond<'tcx>>,
) {
    match &stmt.kind {
        StatementKind::Assign(box (Place { local, .. }, _)) if basic.ghosts.contains(local) => {}
        StatementKind::Assign(box (_, Rvalue::Discriminant(_))) => {
            assert!(stmt_index == basic[bb].statements.len() - 1);
            let terminator = get_terminator(&basic[bb]);
            match &terminator.kind {
                TerminatorKind::SwitchInt { .. } => {}
                _ => panic!("unexpected terminator {:?} for taking discriminant", terminator),
            }
        }
        StatementKind::Assign(box (place, Rvalue::Use(Operand::Copy(place2))))
            if place2.get_ty(mir_access).is_mutable_ptr() =>
        {
            let expr2 = place2.get_mut_expr(env, mir_access);
            let var = Var::MutRet { location: bb, stmt_index };
            let ty_body = match &place2.get_ty(mir_access).kind() {
                TyKind::Ref(_, ty_body, Mutability::Mut) => ty_body,
                _ => unreachable!(),
            };
            let ty_body = Ty::new(ty_body);
            match expr2 {
                Expr::Path(path) => {
                    let ty = place2.get_ty(mir_access);
                    let (cur, ret) = Expr::decompose_mut_path(path);
                    *expr2 = Expr::pair(ty, Expr::from_var(var, ty_body), ret);
                    let new_expr = Expr::pair(ty, cur, Expr::from_var(var, ty_body));
                    place.assign(new_expr, env, conds, mir_access);
                }
                Expr::Aggregate { ty, variant_index: VRT0, fields } => {
                    assert!(fields.len() == 2);
                    let ty = *ty;
                    let new_expr = Expr::from_var(var, ty_body);
                    let old_expr = std::mem::replace(&mut fields[0], new_expr.clone());
                    let new_expr = Expr::pair(ty, old_expr, new_expr);
                    place.assign(new_expr, env, conds, mir_access);
                }
                _ => panic!("unexpected expression {:?} for a mutable reference", expr2),
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
        | StatementKind::Nop => {}
        StatementKind::StorageDead(local) => {
            if let Some(expr) = env.remove(local) {
                expr.do_drop(local.get_ty(mir_access), mir_access, conds);
            }
        }
        _ => panic!("unsupported statement {:?}", stmt),
    }
}

struct FnCall<'a, 'tcx> {
    ty: Ty<'tcx>,
    did: DefId,
    fun_name: String,
    args: &'a [Operand<'tcx>],
    caller: BasicBlock,
    res_place: &'a Place<'tcx>,
    res_ty: Ty<'tcx>,
}

fn gather_conds_from_fun<'tcx>(
    FnCall { args, ty, did, fun_name, caller, res_place, res_ty }: FnCall<'_, 'tcx>,
    mir_access: MirAccess<'tcx>,
    env: &mut Map<Local, Expr<'tcx>>,
    conds: &mut Vec<Cond<'tcx>>,
    fun_asks: &mut Map<String, Ty<'tcx>>,
) {
    if let Some(bin_op) = BinOp::try_from_fun(did) {
        let res = Expr::from_bin_op(
            bin_op,
            args[0].get_expr(env, mir_access),
            args[1].get_expr(env, mir_access),
        );
        res_place.assign(res, env, conds, mir_access);
    } else if let Some(un_op) = UnOp::try_from_fun(did) {
        let res = Expr::UnOp(un_op, Box::new(args[0].get_expr(env, mir_access)));
        res_place.assign(res, env, conds, mir_access);
    } else if fun_name == "<rand>" {
        let res = Expr::from_var(Var::Rand { caller }, res_ty);
        res_place.assign(res, env, conds, mir_access);
    } else if fun_name == "<swap>" {
        assert!(args.len() == 2);
        let (x, x_) = args[0].get_expr(env, mir_access).decompose_mut();
        let (y, y_) = args[1].get_expr(env, mir_access).decompose_mut();
        conds.push(Cond::Eq { tgt: y_, src: x });
        conds.push(Cond::Eq { tgt: x_, src: y });
    } else if fun_name == "<free>" {
        // do nothing
    } else {
        fun_asks.insert(rep_fun_name(ty), ty);
        let mut args: Vec<_> = args.iter().map(|arg| arg.get_expr(env, mir_access)).collect();
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
    data: Data<'_, 'tcx>,
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
            let terminator = get_terminator(&basic[bb]);
            if let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind {
                assert!(!basic.is_ghost_switching(bb));
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
                                let val_expr = Expr::Const(Const::Int(*val as i64));
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
                    DiscriminantKind::Tag => match &discr_ty.kind() {
                        TyKind::Adt(AdtDef { variants, .. }, adt_substs) => {
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
    fun_ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    basic_asks: &mut BasicAsks<'tcx>,
) -> FunDef<'tcx> {
    let mir = tcx.optimized_mir(fun_ty.fun_of_fun_ty());
    let bbds = mir.basic_blocks();
    let mir_access = MirAccess { mir, generic_args: fun_ty.substs_of_fun_ty(), tcx };
    /* preparations */
    let ghosts = get_ghosts(&bbds[BB0], mir.arg_count);
    let basic = Basic { bbds, ghosts: &ghosts };
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
    pub tup_asks: Vec<(String, GenericArgsRef<'tcx>)>,
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
    if let Some((main, EntryFnType::Main)) = tcx.entry_fn(()) {
        let main_ty = tcx.type_of(main);
        let main_ty = Ty::new(main_ty);
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
    while !basic_asks.drop_asks.is_empty() {
        let mut old_drop_asks: Map<String, Ty<'tcx>> = std::mem::take(&mut basic_asks.drop_asks);
        for (drop_name, ty) in old_drop_asks.drain() {
            drop_defs.entry(drop_name).or_insert_with(|| get_drop_def(ty, tcx, &mut basic_asks));
        }
    }
    /* return results */
    let BasicAsks { fun_asks, drop_asks, adt_asks, tup_asks, mut_asks } = basic_asks;
    assert!(fun_asks.is_empty() && drop_asks.is_empty());
    Summary {
        fun_defs: fun_defs.into_sorted_vec(),
        drop_defs: drop_defs.into_sorted_vec(),
        adt_asks: adt_asks.into_sorted_vec(),
        tup_asks: tup_asks.into_sorted_vec(),
        mut_asks: mut_asks.into_sorted_vec(),
    }
}
