use std::collections::HashMap;
use std::mem::swap;

use crate::prettify::pr_fun_name;
use crate::represent::rep_fun_name;
use crate::types::{
  AdtDef, BasicBlock, DefId, EntryFnType, FieldDef, FieldIdx, GenericArgsRef, Local, Map,
  Mutability, Operand, Place, Rvalue, Set, Statement, StatementKind, TerminatorKind, Ty, TyCtxt,
  TyKind, VariantDef,
};
use crate::util::{get_tmnt, BB0, FLD0, FLD1, VRT0, _0};

pub mod graph;
use graph::{get_ghosts, Basic};

pub mod data;
use data::{
  assign_to_place, drop_expr, read_opd, read_place, read_rvalue, seize_place, set_tag,
  traverse_prerule, BasicAsks, BinOp, Cond, Const, End, Env, Expr, MirAccess, MirAccessCtxExt,
  MirAccessExt, Path, UnOp, Var,
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
    Prerule { init_env, mut conds, mut end }: Prerule<'tcx>, mir_access: MirAccess<'tcx>,
    is_main: bool, basic_asks: &mut BasicAsks<'tcx>,
  ) -> Self {
    let mut args = init_env.into_iter().map(|(_, expr)| expr).collect::<Vec<_>>();
    let res_ty = _0.get_ty(mir_access);
    if !res_ty.is_unit() {
      args.push(Expr::from_var(Var::SelfResult, res_ty));
    }
    if is_main {
      args.push(Expr::from_var(Var::SelfPanic, mir_access.get_bool()));
    }
    let vars = traverse_prerule(&mut args, &mut conds, &mut end, mir_access, basic_asks);
    Rule { vars, args, conds, end }
  }
}

#[derive(Debug)]
pub struct PivotDef<'tcx> {
  pub param_tys: Vec<Ty<'tcx>>,
  pub rules: Vec<Rule<'tcx>>,
}
/// A unit corresponding to predicates to be generated
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
    match &get_tmnt(bbd).kind {
      TerminatorKind::SwitchInt { discr, .. } if !basic.is_ghost_switching(pivot) => {
        match bbd.statements.last() {
          Some(Statement {
            kind: StatementKind::Assign(box (_, Rvalue::Discriminant(place))),
            ..
          }) => (*place, DiscriminantKind::Tag),
          _ => match discr {
            Operand::Copy(place) | Operand::Move(place) => (*place, DiscriminantKind::Value),
            Operand::Constant(..) => panic!("unexpected operand {:?} for a discriminant", discr),
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
  init_env: Env<'tcx>, is_main: bool, pivot: BasicBlock, mut conds: Vec<Cond<'tcx>>,
  mut env: Env<'tcx>, data: Data<'_, 'tcx>,
) -> Prerule<'tcx> {
  let Data { mir_access, .. } = data;
  let mut args = Vec::<Expr<'tcx>>::new();
  for local in data.get_locals(Pivot::Switch(pivot)).clone() {
    args.push(env.remove(&local).unwrap_or_else(|| Expr::nonce(local.get_ty(mir_access))));
  }
  for (local, expr) in env {
    drop_expr(local.get_ty(mir_access), &expr, &mut conds, mir_access);
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
  is_main: bool, init_me: BasicBlock, init_env: Env<'tcx>, data: Data<'_, 'tcx>,
  fun_asks: &mut Map<String, Ty<'tcx>>,
) -> Prerule<'tcx> {
  let mut me = init_me;
  let mut conds = Vec::<Cond<'tcx>>::new();
  let mut env = init_env.clone();
  let Data { basic, mir_access, .. } = data;
  loop {
    if let TerminatorKind::Call { destination: None, .. } = &get_tmnt(&basic[me]).kind {
      for (local, expr) in env {
        drop_expr(local.get_ty(mir_access), &expr, &mut conds, mir_access);
      }
      return Prerule { init_env, conds, end: End::Panic };
    }
    for (stmt_index, stmt) in basic[me].statements.iter().enumerate() {
      match &stmt.kind {
        StatementKind::Assign(box (Place { local, .. }, _)) if basic.ghosts.contains(local) => {}
        StatementKind::Assign(box (_, Rvalue::Discriminant(_))) => {
          assert!(stmt_index == basic[me].statements.len() - 1);
          let tmnt = get_tmnt(&basic[me]);
          match &tmnt.kind {
            TerminatorKind::SwitchInt { .. } => {}
            _ => panic!("unexpected terminator {:?} for taking discriminant", tmnt),
          }
        }
        StatementKind::Assign(box (place, Rvalue::Use(Operand::Copy(place2))))
          if place2.get_ty(mir_access).is_mutable_ptr() =>
        {
          let expr2 = seize_place(place2, &mut env, mir_access);
          let var = Var::MutRet(me, stmt_index);
          let ty_body = match &place2.get_ty(mir_access).kind() {
            TyKind::Ref(_, ty_body, Mutability::Mut) => ty_body,
            _ => unreachable!(),
          };
          let ty_body = Ty::new(ty_body);
          match expr2 {
            Expr::Path(path) => {
              let ty = place2.get_ty(mir_access);
              let cur = Expr::Path(path.get_proj(ty, VRT0, FLD0));
              let ret = Expr::Path(path.get_proj(ty, VRT0, FLD1));
              *expr2 = Expr::Aggregate(ty, VRT0, vec![Expr::from_var(var, ty_body), ret]);
              let new_expr = Expr::Aggregate(ty, VRT0, vec![cur, Expr::from_var(var, ty_body)]);
              assign_to_place(place, new_expr, &mut env, &mut conds, mir_access);
            }
            Expr::Aggregate(ty, VRT0, flds) => {
              assert!(flds.len() == 2);
              let mut expr_buf = Expr::from_var(var, ty_body);
              swap(&mut flds[FLD0.index()], &mut expr_buf);
              let new_expr =
                Expr::Aggregate(*ty, VRT0, vec![expr_buf, Expr::from_var(var, ty_body)]);
              assign_to_place(place, new_expr, &mut env, &mut conds, mir_access);
            }
            _ => panic!("unexpected expression {:?} for a mutable reference", expr2),
          }
        }
        StatementKind::Assign(box (place, rvalue)) => {
          let expr = read_rvalue(rvalue, &mut env, mir_access, me, stmt_index);
          assign_to_place(place, expr, &mut env, &mut conds, mir_access);
        }
        StatementKind::SetDiscriminant { place, variant_index } => {
          set_tag(place, *variant_index, &mut env, mir_access);
        }
        StatementKind::StorageLive(_)
        | StatementKind::AscribeUserType(_, _)
        | StatementKind::Nop => {}
        StatementKind::StorageDead(local) => {
          if let Some(expr) = env.remove(local) {
            drop_expr(local.get_ty(mir_access), &expr, &mut conds, mir_access);
          }
        }
        _ => panic!("unsupported statement {:?}", stmt),
      }
    }
    let tmnt = get_tmnt(&basic[me]);
    match &tmnt.kind {
      TerminatorKind::Goto { target } if *target == me => {
        return Prerule { init_env, conds, end: End::NeverReturn };
      }
      TerminatorKind::Goto { target }
      | TerminatorKind::Drop { target, .. }
      | TerminatorKind::Assert { target, .. } => {
        me = *target;
        continue;
      }
      TerminatorKind::Return => {
        let mut res: Option<Expr> = None;
        for (local, expr) in env {
          if local == _0 {
            res = Some(expr);
          } else {
            drop_expr(local.get_ty(mir_access), &expr, &mut conds, mir_access);
          }
        }
        return Prerule { init_env, conds, end: End::Return { res } };
      }
      TerminatorKind::Call { func, args, destination: Some((place, target)), .. } => {
        let fun_ty = func.get_ty(mir_access);
        let fun = fun_ty.fun_of_fun_ty();
        let fun_name = pr_fun_name(fun);
        let res_ty = place.get_ty(mir_access);
        if let Some(bin_op) = BinOp::try_from_fun(fun) {
          assert!(args.len() == 2);
          let res = Expr::from_bin_op(
            bin_op,
            read_opd(&args[0], &mut env, mir_access),
            read_opd(&args[1], &mut env, mir_access),
          );
          assign_to_place(place, res, &mut env, &mut conds, mir_access);
        } else if let Some(un_op) = UnOp::try_from_fun(fun) {
          assert!(args.len() == 1);
          let res = Expr::UnOp(un_op, Box::new(read_opd(&args[0], &mut env, mir_access)));
          assign_to_place(place, res, &mut env, &mut conds, mir_access);
        } else if fun_name == "<rand>" {
          assign_to_place(
            place,
            Expr::from_var(Var::Rand(me), res_ty),
            &mut env,
            &mut conds,
            mir_access,
          );
        } else if fun_name == "<swap>" {
          assert!(args.len() == 2);
          let (x, x_) = read_opd(&args[0], &mut env, mir_access).decompose_mut();
          let (y, y_) = read_opd(&args[1], &mut env, mir_access).decompose_mut();
          conds.push(Cond::Eq { tgt: y_, src: x });
          conds.push(Cond::Eq { tgt: x_, src: y });
        } else if fun_name == "<free>" {
          // do nothing
        } else {
          fun_asks.insert(rep_fun_name(fun_ty), fun_ty);
          let mut args: Vec<_> =
            args.iter().map(|arg| read_opd(arg, &mut env, mir_access)).collect();
          if !res_ty.is_unit() {
            let res = Expr::from_var(Var::CallResult(me), res_ty);
            assign_to_place(place, res.clone(), &mut env, &mut conds, mir_access);
            args.push(res.clone());
          }
          conds.push(Cond::Call { fun_ty, args });
        }
        me = *target;
        continue;
      }
      TerminatorKind::SwitchInt { targets, .. } => {
        if basic.is_ghost_switching(me) {
          me = targets.all_targets()[0];
          continue;
        }
        return pivot_up(init_env, is_main, me, conds, env, data);
      }
      _ => panic!("unexpected terminator {:?}", tmnt),
    }
  }
}

fn analyze_pivot<'tcx>(
  is_main: bool, pivot: Pivot, data: Data<'_, 'tcx>, basic_asks: &mut BasicAsks<'tcx>,
) -> PivotDef<'tcx> {
  let Data { basic, mir_access, .. } = data;
  let BasicAsks { fun_asks, .. } = basic_asks;
  let mut prerules = Vec::<Prerule<'tcx>>::new();
  let param_tys = data.get_param_tys(is_main, pivot);
  let env = data
    .get_locals(pivot)
    .clone()
    .into_iter()
    .map(|local| (local, Expr::Path(Path::Var(Var::Input(local), local.get_ty(mir_access)))))
    .collect::<HashMap<_, _>>();
  let env = Env::from_inner(env);
  if let Pivot::Switch(me) = pivot {
    let tmnt = get_tmnt(&basic[me]);
    match &tmnt.kind {
      TerminatorKind::SwitchInt { targets, .. } => {
        assert!(!basic.is_ghost_switching(me));
        let (discr_place, discr_kind) = data.place_discriminant_kind(me);
        let discr_ty = discr_place.get_ty(mir_access);
        let main_targets = targets.iter().collect::<Vec<_>>();
        let rest_target = targets.otherwise();
        match discr_kind {
          DiscriminantKind::Value => match &discr_ty.kind() {
            TyKind::Bool => {
              assert!(main_targets.len() == 1 && main_targets[0].0 == 0);
              for (b, tgt) in [(false, &main_targets[0].1), (true, &rest_target)] {
                let mut env = env.clone();
                *seize_place(&discr_place, &mut env, mir_access) = Expr::Const(Const::Bool(b));
                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
              }
            }
            TyKind::Int(_) | TyKind::Uint(_) => {
              let mut neq_srcs = vec![];
              for (val, tgt) in &main_targets {
                let mut env = env.clone();
                let val_expr = Expr::Const(Const::Int(*val as i64));
                *seize_place(&discr_place, &mut env, mir_access) = val_expr.clone();
                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
                neq_srcs.push(val_expr);
              }
              let neq_tgt = read_place(&discr_place, &env, mir_access);
              let mut prerule = get_prerule(is_main, rest_target, env, data, fun_asks);
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
                      Var::Split(me, variant_index, FieldIdx::from(field_index)),
                      fld_def.get_ty_with(mir_access, adt_substs),
                    )
                  })
                  .collect::<Vec<_>>();
                *seize_place(&discr_place, &mut env, mir_access) =
                  Expr::Aggregate(discr_ty, variant_index, args);
                prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
              }
            }
            _ => panic!("unexpected tag branching for a non-adt type {:?}", discr_ty),
          },
        }
      }
      _ => panic!("unexpected terminator {:?} for a pivot", tmnt),
    }
  } else {
    prerules.push(get_prerule(is_main, BB0, env.clone(), data, fun_asks));
  }
  let rules = prerules
    .into_iter()
    .map(|prerule| Rule::from_prerule(prerule, mir_access, is_main, basic_asks))
    .collect();
  PivotDef { param_tys, rules }
}

fn analyze_fun<'tcx>(
  fun_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, basic_asks: &mut BasicAsks<'tcx>,
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
  fun_def.into_inner_vec()
}

pub struct Summary<'tcx> {
  pub fun_defs: Vec<(String, FunDef<'tcx>)>,
  pub drop_defs: Vec<(String, FunDef<'tcx>)>,
  pub adt_asks: Vec<DefId>,
  pub tup_asks: Vec<(String, GenericArgsRef<'tcx>)>,
  pub mut_asks: Vec<(String, Ty<'tcx>)>,
}

fn get_drop_def<'tcx>(
  _ty: Ty<'tcx>, _tcx: TyCtxt<'tcx>, _basic_asks: &mut BasicAsks<'tcx>,
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
    let fun_asks = std::mem::take(&mut basic_asks.fun_asks).into_inner_vec();
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
    let mut old_drop_asks: Map<String, Ty<'tcx>> = Map::new();
    swap(&mut basic_asks.drop_asks, &mut old_drop_asks);
    for (drop_name, ty) in old_drop_asks.drain() {
      drop_defs.entry(drop_name).or_insert_with(|| get_drop_def(ty, tcx, &mut basic_asks));
    }
  }
  /* return results */
  let BasicAsks { fun_asks, drop_asks, adt_asks, tup_asks, mut_asks } = basic_asks;
  assert!(fun_asks.is_empty() && drop_asks.is_empty());
  Summary {
    fun_defs: fun_defs.into_inner_vec(),
    drop_defs: drop_defs.into_inner_vec(),
    adt_asks: adt_asks.into_inner_vec(),
    tup_asks: tup_asks.into_inner_vec(),
    mut_asks: mut_asks.into_inner_vec(),
  }
}
