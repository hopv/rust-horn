use rustc_middle::mir::{
  BasicBlock as BB, BasicBlockData as BBD, Local, Operand, Place, Rvalue, StatementKind as StmtK,
  TerminatorKind as TmntK,
};
use rustc_middle::ty::TyKind as TyK;

use std::collections::{HashMap as Map, HashSet as Set};
use std::ops::Index;

use crate::util::{enumerate_bbds, get_tmnt, BBDs, BB0};

pub fn get_ghosts(bbd0: &BBD, n_args: usize) -> Set<Local> {
  let mut ghosts: Set<Local> = Set::new();
  for stmt in bbd0.statements.iter() {
    if let StmtK::Assign(box (Place { local, .. }, Rvalue::Use(Operand::Constant(constant)))) =
      &stmt.kind
    {
      if let TyK::Bool = &constant.literal.ty().kind() {
        if local.index() > n_args {
          ghosts.insert(*local);
          continue;
        }
      } else {
        panic!("spurious ghost")
      }
    }
    break;
  }
  ghosts
}

#[derive(Copy, Clone)]
pub struct Basic<'a, 'tcx> {
  pub bbds: &'a BBDs<'tcx>,
  pub ghosts: &'a Set<Local>,
}
impl<'tcx> Index<BB> for Basic<'_, 'tcx> {
  type Output = BBD<'tcx>;
  fn index(&self, bb: BB) -> &Self::Output { &self.bbds[bb] }
}
impl<'a, 'tcx> Basic<'a, 'tcx> {
  pub fn is_ghost_switching(self, bb: BB) -> bool {
    match &get_tmnt(&self[bb]).kind {
      TmntK::SwitchInt { targets, discr, .. } => {
        if let Operand::Copy(Place { local, .. }) = discr {
          if self.ghosts.contains(local) {
            assert!(targets.all_targets().len() == 2);
            return true;
          }
        }
      }
      _ => {}
    }
    false
  }
  pub fn is_panicking(self, bb: BB) -> bool {
    match &get_tmnt(&self[bb]).kind {
      TmntK::Call { destination: None, .. } | TmntK::Abort | TmntK::Unreachable => true,
      _ => false,
    }
  }
  pub fn get_targets(self, bb: BB) -> Vec<BB> {
    let tmnt = get_tmnt(&self[bb]);
    match &tmnt.kind {
      TmntK::Goto { target } | TmntK::Drop { target, .. } | TmntK::Assert { target, .. } => {
        vec![*target]
      }
      TmntK::Unreachable | TmntK::Return | TmntK::Call { destination: None, .. } => vec![],
      TmntK::SwitchInt { targets, .. } => {
        let targets = targets.all_targets();
        if self.is_ghost_switching(bb) {
          vec![targets[0]]
        } else {
          targets.to_vec()
        }
      }
      TmntK::Call { destination: Some((_, target)), .. } => vec![*target],
      _ => panic!("unsupported terminator {:?}", tmnt),
    }
  }
}

pub fn get_pivots(basic: Basic) -> Vec<BB> {
  let mut pivots = Vec::<BB>::new();
  for (bb, bbd) in enumerate_bbds(basic.bbds) {
    let tmnt = get_tmnt(&bbd);
    match &tmnt.kind {
      TmntK::Goto { .. }
      | TmntK::Drop { .. }
      | TmntK::Assert { .. }
      | TmntK::Unreachable
      | TmntK::Return
      | TmntK::Call { .. } => {}
      TmntK::SwitchInt { .. } => {
        pivots.push(bb);
      }
      _ => panic!("unsupported terminator {:?}", tmnt),
    }
  }
  pivots.sort_unstable();
  pivots
}

pub fn get_ins_outs_map(
  basic: Basic, n_init_ins: usize,
) -> (Map<BB, Set<Local>>, Map<BB, Set<Local>>) {
  let mut ins_map = Map::<BB, Set<Local>>::new();
  fn dfs(
    me: BB, ins: &Set<Local>, discr_local: Option<Local>, basic: Basic,
    ins_map: &mut Map<BB, Set<Local>>,
  ) {
    let mut ins = ins.clone();
    /* shrink */
    if basic.is_panicking(me) {
      ins.clear();
    }
    for stmt in basic[me].statements.iter() {
      if let StmtK::StorageDead(local) = &stmt.kind {
        if Some(*local) != discr_local {
          ins.remove(local);
        }
      } else {
        break;
      }
    }
    /* return or shrink further */
    if let Some(ins_ex) = ins_map.get(&me) {
      if ins_ex.is_subset(&ins) {
        return;
      } else {
        ins.retain(|local| ins_ex.contains(local));
      }
    }
    /* calc */
    ins_map.insert(me, ins.clone());
    for stmt in basic[me].statements.iter() {
      match &stmt.kind {
        StmtK::Assign(box (Place { local, .. }, _)) if basic.ghosts.contains(local) => {}
        StmtK::Assign(box (_, Rvalue::Discriminant(_))) => {}
        StmtK::Assign(box (Place { local, .. }, _)) => {
          ins.insert(*local);
        }
        StmtK::SetDiscriminant { place: box Place { local, .. }, .. } => {
          ins.insert(*local);
        }
        StmtK::StorageLive(_) => {}
        StmtK::StorageDead(local) => {
          ins.remove(local);
        }
        _ => panic!("unsupported statement {:?}", stmt),
      }
    }
    let tmnt = get_tmnt(&basic[me]);
    let mut discr_local = None::<Local>;
    match &tmnt.kind {
      TmntK::Goto { .. }
      | TmntK::Return
      | TmntK::Drop { .. }
      | TmntK::Assert { .. }
      | TmntK::Unreachable => {}

      TmntK::SwitchInt { discr, .. } => match discr {
        Operand::Copy(place) | Operand::Move(place) => discr_local = Some(place.local),
        _ => panic!("unexpected discriminant {:?}", discr),
      },
      TmntK::Call { destination, .. } => {
        if let Some((Place { local, .. }, _)) = destination {
          ins.insert(*local);
        }
      }
      _ => panic!("unsupported terminator {:?}", tmnt),
    }
    for him in basic.get_targets(me) {
      dfs(him, &ins, discr_local, basic, ins_map);
    }
  }
  let mut init_ins: Set<Local> = Set::new();
  for i in 1..n_init_ins + 1 {
    init_ins.insert(Local::from(i));
  }
  dfs(BB0, &init_ins, None, basic, &mut ins_map);
  let mut outs_map = Map::<BB, Set<Local>>::new();
  for (me, _) in enumerate_bbds(basic.bbds) {
    let mut outs = Set::<Local>::new();
    for him in basic.get_targets(me) {
      for local in ins_map[&him].iter() {
        outs.insert(*local);
      }
    }
    outs_map.insert(me, outs);
  }
  (ins_map, outs_map)
}
