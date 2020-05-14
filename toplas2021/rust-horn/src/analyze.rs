use rustc_hir::def_id::{CrateNum, DefId};
use rustc_hir::Mutability;
use rustc_middle::mir::{
  BasicBlock as BB, Field as FldIdx, Local, Operand, Place, Rvalue, Statement,
  StatementKind as StmtK, TerminatorKind as TmntK,
};
use rustc_middle::ty::subst::InternalSubsts as Substs;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind as TyK, VariantDef as VrtDef};
use rustc_session::config::EntryFnType;

use std::collections::{HashMap as Map, HashSet as Set};
use std::mem::swap;

use crate::prettify::pr_fun_name;
use crate::represent::rep_fun_name;
use crate::util::{
  fun_of_fun_ty, get_tmnt, sort_map, sort_set, substs_of_fun_ty, BB0, FLD0, FLD1, VRT0, _0,
};

pub mod graph;
use graph::{get_ghosts, get_ins_outs_map, get_pivots, Basic};

pub mod data;
use data::{
  assign_to_place, bin_op_expr, decompose_mut, drop_expr, fun_to_bin_op, fun_to_un_op, get_proj,
  is_fun_swap, is_fun_vacuous, nonce, read_opd, read_rvalue, seize_place, set_tag,
  traverse_prerule, var_to_expr, BasicAsks, Cond, Const, End, Env, Expr, Outer, Var,
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
#[derive(Debug)]
pub struct PivotDef<'tcx> {
  pub param_tys: Vec<Ty<'tcx>>,
  pub rules: Vec<Rule<'tcx>>,
}

pub type FunDef<'tcx> = Vec<(Option<BB>, PivotDef<'tcx>)>;

#[derive(Debug, Copy, Clone)]
enum DiscrKind {
  Value,
  Tag,
}

#[derive(Copy, Clone)]
struct Data<'a, 'tcx> {
  ins_map: &'a Map<BB, Set<Local>>,
  outs_map: &'a Map<BB, Set<Local>>,
  basic: Basic<'a, 'tcx>,
  outer: Outer<'tcx>,
}
impl<'a, 'tcx> Data<'a, 'tcx> {
  fn get_locals(self, pivot: Option<BB>) -> &'a Set<Local> {
    let Data { ins_map, outs_map, .. } = self;
    if let Some(bb) = pivot {
      &outs_map[&bb]
    } else {
      &ins_map[&BB0]
    }
  }
  fn discr_place_kind(self, pivot: BB) -> (Place<'tcx>, DiscrKind) {
    let Data { basic, .. } = self;
    let bbd = &basic[pivot];
    match &get_tmnt(bbd).kind {
      TmntK::SwitchInt { discr, .. } if !basic.is_ghost_switching(pivot) => {
        match bbd.statements.last() {
          Some(Statement { kind: StmtK::Assign(box (_, Rvalue::Discriminant(place))), .. }) => {
            (place.clone(), DiscrKind::Tag)
          }
          _ => match discr {
            Operand::Copy(place) | Operand::Move(place) => (place.clone(), DiscrKind::Value),
            _ => panic!("unexpected operand {:?} for a discriminant", discr),
          },
        }
      }
      _ => panic!("unexpected type of pivot for a discriminant"),
    }
  }
  fn get_param_tys(self, is_main: bool, pivot: Option<BB>) -> Vec<Ty<'tcx>> {
    let Data { outer, .. } = self;
    let locals = sort_set(self.get_locals(pivot).clone());
    let mut res = locals.iter().map(|local| outer.local_to_ty(*local)).collect::<Vec<_>>();
    let res_ty = outer.local_to_ty(_0);
    if !res_ty.is_unit() {
      res.push(res_ty);
    }
    if is_main {
      res.push(outer.get_bool());
    }
    res
  }
}

fn pivot_up<'tcx>(
  init_env: Env<'tcx>, is_main: bool, pivot: BB, mut conds: Vec<Cond<'tcx>>, mut env: Env<'tcx>,
  data: Data<'_, 'tcx>,
) -> Prerule<'tcx>
{
  let Data { outer, .. } = data;
  let mut args = Vec::<Expr<'tcx>>::new();
  for local in sort_set(data.get_locals(Some(pivot)).clone()).iter() {
    args.push(if let Some(expr) = env.remove(local) {
      expr
    } else {
      nonce(outer.local_to_ty(*local))
    });
  }
  for (local, expr) in sort_map(env).drain(..) {
    drop_expr(outer.local_to_ty(local), &expr, &mut conds, outer);
  }
  let res_ty = outer.local_to_ty(_0);
  if !res_ty.is_unit() {
    args.push(var_to_expr(Var::SelfResult, res_ty));
  }
  if is_main {
    args.push(var_to_expr(Var::SelfPanic, outer.get_bool()));
  }
  Prerule { init_env, conds, end: End::Pivot { pivot, args } }
}
fn get_prerule<'tcx>(
  is_main: bool, init_me: BB, init_env: Env<'tcx>, data: Data<'_, 'tcx>,
  fun_asks: &mut Map<String, Ty<'tcx>>,
) -> Prerule<'tcx>
{
  let mut me = init_me;
  let mut conds = Vec::<Cond<'tcx>>::new();
  let mut env = init_env.clone();
  let Data { basic, outer, .. } = data;
  loop {
    if let TmntK::Call { destination: None, .. } = &get_tmnt(&basic[me]).kind {
      return Prerule { init_env, conds, end: End::Panic };
    }
    for (stmt_idx, stmt) in basic[me].statements.iter().enumerate() {
      match &stmt.kind {
        StmtK::Assign(box (Place { local, .. }, _)) if basic.ghosts.contains(local) => {}
        StmtK::Assign(box (_, Rvalue::Discriminant(_))) => {
          assert!(stmt_idx == basic[me].statements.len() - 1);
          let tmnt = get_tmnt(&basic[me]);
          match &tmnt.kind {
            TmntK::SwitchInt { .. } => {}
            _ => panic!("unexpected terminator {:?} for taking discriminant", tmnt),
          }
        }
        StmtK::Assign(box (place, Rvalue::Use(Operand::Copy(place2))))
          if outer.place_to_ty(place2).is_mutable_ptr() =>
        {
          let expr2 = seize_place(place2, &mut env, outer);
          let var = Var::MutRet(me, stmt_idx);
          let ty_body = match &outer.place_to_ty(place2).kind {
            TyK::Ref(_, ty_body, Mutability::Mut) => ty_body,
            _ => unreachable!(),
          };
          match expr2 {
            Expr::Path(path) => {
              let ty = outer.place_to_ty(place2);
              let cur = Expr::Path(get_proj(ty, VRT0, FLD0, path.clone()));
              let ret = Expr::Path(get_proj(ty, VRT0, FLD1, path.clone()));
              *expr2 = Expr::Aggr(ty, VRT0, vec![var_to_expr(var, ty_body), ret]);
              let new_expr = Expr::Aggr(ty, VRT0, vec![cur, var_to_expr(var, ty_body)]);
              assign_to_place(place, new_expr, &mut env, &mut conds, outer);
            }
            Expr::Aggr(ty, VRT0, flds) => {
              assert!(flds.len() == 2);
              let mut expr_buf = var_to_expr(var, ty_body);
              swap(&mut flds[FLD0.index()], &mut expr_buf);
              let new_expr = Expr::Aggr(ty, VRT0, vec![expr_buf, var_to_expr(var, ty_body)]);
              assign_to_place(place, new_expr, &mut env, &mut conds, outer);
            }
            _ => panic!("unexpected expression {:?} for a mutable reference", expr2),
          }
        }
        StmtK::Assign(box (place, rvalue)) => {
          let expr = read_rvalue(rvalue, &mut env, outer, me, stmt_idx);
          assign_to_place(place, expr, &mut env, &mut conds, outer);
        }
        StmtK::SetDiscriminant { place, variant_index } => {
          set_tag(place, *variant_index, &mut env, outer);
        }
        StmtK::StorageLive(_) | StmtK::AscribeUserType(_, _) | StmtK::Nop => {}
        StmtK::StorageDead(local) => {
          if let Some(expr) = env.remove(local) {
            drop_expr(outer.local_to_ty(*local), &expr, &mut conds, outer);
          }
        }
        _ => panic!("unsupported statement {:?}", stmt),
      }
    }
    let tmnt = get_tmnt(&basic[me]);
    match &tmnt.kind {
      TmntK::Goto { target } if *target == me => {
        return Prerule { init_env, conds, end: End::NeverReturn };
      }
      TmntK::Goto { target } | TmntK::Drop { target, .. } | TmntK::Assert { target, .. } => {
        me = *target;
        continue;
      }
      TmntK::Return => {
        let mut res: Option<Expr> = None;
        for (local, expr) in env.drain() {
          if local != _0 {
            drop_expr(outer.local_to_ty(local), &expr, &mut conds, outer);
          } else {
            res = Some(expr);
          }
        }
        return Prerule { init_env, conds, end: End::Return { res } };
      }
      TmntK::Call { func, args, destination: Some((place, target)), .. } => {
        let fun_ty = outer.opd_to_ty(func);
        let fun = fun_of_fun_ty(fun_ty);
        let res_ty = outer.place_to_ty(place);
        if let Some(bin_op) = fun_to_bin_op(fun) {
          assert!(args.len() == 2);
          let res = bin_op_expr(
            bin_op,
            read_opd(&args[0], &mut env, outer),
            read_opd(&args[1], &mut env, outer),
          );
          assign_to_place(place, res, &mut env, &mut conds, outer);
        } else if let Some(un_op) = fun_to_un_op(fun) {
          assert!(args.len() == 1);
          let res = Expr::UnOp(un_op, box read_opd(&args[0], &mut env, outer));
          assign_to_place(place, res, &mut env, &mut conds, outer);
        } else if pr_fun_name(fun) == "<rand>" {
          assign_to_place(place, var_to_expr(Var::Rand(me), res_ty), &mut env, &mut conds, outer);
        } else if is_fun_swap(fun) {
          assert!(args.len() == 2);
          let (x, x_) = decompose_mut(read_opd(&args[0], &mut env, outer));
          let (y, y_) = decompose_mut(read_opd(&args[1], &mut env, outer));
          conds.push(Cond::Eq { tgt: y_, src: x });
          conds.push(Cond::Eq { tgt: x_, src: y });
        } else if is_fun_vacuous(fun) {
          // do nothing
        } else {
          fun_asks.insert(rep_fun_name(fun_ty), fun_ty);
          let mut args: Vec<_> = args.iter().map(|arg| read_opd(arg, &mut env, outer)).collect();
          if !res_ty.is_unit() {
            let res = var_to_expr(Var::CallResult(me), res_ty);
            assign_to_place(place, res.clone(), &mut env, &mut conds, outer);
            args.push(res.clone());
          }
          conds.push(Cond::Call { fun_ty, args });
        }
        me = *target;
        continue;
      }
      TmntK::SwitchInt { targets, .. } => {
        if basic.is_ghost_switching(me) {
          me = targets[0];
          continue;
        }
        return pivot_up(init_env, is_main, me, conds, env, data);
      }
      _ => panic!("unexpected terminator {:?}", tmnt),
    }
  }
}
fn analyze_pivot<'tcx>(
  is_main: bool, pivot: Option<BB>, data: Data<'_, 'tcx>, basic_asks: &mut BasicAsks<'tcx>,
) -> PivotDef<'tcx> {
  let Data { basic, outer, .. } = data;
  let BasicAsks { fun_asks, .. } = basic_asks;
  let mut prerules = Vec::<Prerule<'tcx>>::new();
  let param_tys = data.get_param_tys(is_main, pivot);
  let env = data
    .get_locals(pivot)
    .iter()
    .map(|local| (*local, outer.local_to_expr(*local)))
    .collect::<Map<_, _>>();
  if let Some(me) = pivot {
    let tmnt = get_tmnt(&basic[me]);
    match &tmnt.kind {
      TmntK::SwitchInt { values, targets, .. } => {
        assert!(!basic.is_ghost_switching(me));
        let (discr_place, discr_kind) = data.discr_place_kind(me);
        let discr_ty = outer.place_to_ty(&discr_place);
        match discr_kind {
          DiscrKind::Value => match &discr_ty.kind {
            TyK::Bool => {
              if values == &vec![0] && targets.len() == 2 {
                for (tgt, b) in targets.iter().zip([false, true].iter()) {
                  let mut env = env.clone();
                  *seize_place(&discr_place, &mut env, outer) = Expr::Const(Const::Bool(*b));
                  prerules.push(get_prerule(is_main, *tgt, env, data, fun_asks));
                }
              } else {
                unimplemented!("unexpected branching for boolean")
              }
            }
            _ => unimplemented!("value branching for non-boolean is not supported yet"),
          },
          DiscrKind::Tag => match &discr_ty.kind {
            TyK::Adt(AdtDef { variants, .. }, adt_substs) => {
              assert!(variants.len() == values.len());
              for i in 0..values.len() {
                assert!(values[i] == i as u128);
              }
              for ((vrt_idx, VrtDef { fields, .. }), tgt) in
                variants.iter_enumerated().zip(targets.iter())
              {
                let mut env = env.clone();
                let args = fields
                  .iter()
                  .enumerate()
                  .map(|(fld_idx, fld_def)| {
                    var_to_expr(
                      Var::Split(me, vrt_idx, FldIdx::from(fld_idx)),
                      outer.fld_def_to_ty(fld_def, adt_substs),
                    )
                  })
                  .collect::<Vec<_>>();
                *seize_place(&discr_place, &mut env, outer) = Expr::Aggr(discr_ty, vrt_idx, args);
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
    .drain(..)
    .map(|Prerule { init_env, mut conds, mut end }| {
      let mut args = sort_map(init_env).drain(..).map(|(_, expr)| expr).collect::<Vec<_>>();
      let res_ty = outer.local_to_ty(_0);
      if !res_ty.is_unit() {
        args.push(var_to_expr(Var::SelfResult, res_ty));
      }
      if is_main {
        args.push(var_to_expr(Var::SelfPanic, outer.get_bool()));
      }
      let vars = traverse_prerule(&mut args, &mut conds, &mut end, outer, basic_asks);
      Rule { vars, args, conds, end }
    })
    .collect();
  PivotDef { param_tys, rules }
}
fn analyze_fun<'tcx>(
  fun_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, basic_asks: &mut BasicAsks<'tcx>,
) -> FunDef<'tcx> {
  let mir = tcx.optimized_mir(fun_of_fun_ty(fun_ty));
  let bbds = mir.basic_blocks();
  let outer = Outer { mir, substs: substs_of_fun_ty(fun_ty), tcx };
  /* preparations */
  let ghosts = get_ghosts(&bbds[BB0], mir.arg_count);
  let basic = Basic { bbds, ghosts: &ghosts };
  let (ins_map, outs_map) = get_ins_outs_map(basic, mir.arg_count);
  let data = Data { ins_map: &ins_map, outs_map: &outs_map, basic, outer };
  /* wrap up */
  let mut fun_def = Map::<Option<BB>, PivotDef<'tcx>>::new();
  let is_main = &rep_fun_name(fun_ty) == "%main";
  fun_def.insert(None, analyze_pivot(is_main, None, data, basic_asks));
  for pivot in get_pivots(basic) {
    fun_def.insert(Some(pivot), analyze_pivot(is_main, Some(pivot), data, basic_asks));
  }
  sort_map(fun_def)
}

pub struct Summary<'tcx> {
  pub fun_defs: Vec<(String, FunDef<'tcx>)>,
  pub drop_defs: Vec<(String, FunDef<'tcx>)>,
  pub adt_asks: Vec<DefId>,
  pub tup_asks: Vec<(String, &'tcx Substs<'tcx>)>,
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
  if let Some((main, EntryFnType::Main)) = tcx.entry_fn(CrateNum::new(0)) {
    let main_ty = tcx.type_of(main);
    let main_name = rep_fun_name(main_ty);
    fun_defs.insert(main_name, analyze_fun(main_ty, tcx, &mut basic_asks));
  } else {
    panic!("no main function!");
  }
  /* analyze required functions */
  loop {
    let mut fun_asks = basic_asks.fun_asks.drain().collect::<Map<_, _>>();
    if fun_asks.is_empty() {
      break;
    }
    for (fun_name, fun_ty) in fun_asks.drain() {
      if !fun_defs.contains_key(&fun_name) {
        fun_defs.insert(fun_name, analyze_fun(fun_ty, tcx, &mut basic_asks));
      }
    }
  }
  /* added drop functions */
  let mut drop_defs: Map<String, FunDef<'tcx>> = Map::new();
  while !basic_asks.drop_asks.is_empty() {
    let mut old_drop_asks: Map<String, Ty<'tcx>> = Map::new();
    swap(&mut basic_asks.drop_asks, &mut old_drop_asks);
    for (drop_name, ty) in old_drop_asks.drain() {
      if !drop_defs.contains_key(&drop_name) {
        drop_defs.insert(drop_name, get_drop_def(ty, tcx, &mut basic_asks));
      }
    }
  }
  /* return results */
  let BasicAsks { fun_asks, drop_asks, adt_asks, tup_asks, mut_asks } = basic_asks;
  assert!(fun_asks.is_empty() && drop_asks.is_empty());
  Summary {
    fun_defs: sort_map(fun_defs),
    drop_defs: sort_map(drop_defs),
    adt_asks: sort_set(adt_asks),
    tup_asks: sort_map(tup_asks),
    mut_asks: sort_map(mut_asks),
  }
}
