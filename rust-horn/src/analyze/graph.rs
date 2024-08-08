use std::ops::Index;

use crate::types::{
    BasicBlock, BasicBlockData, BasicBlockDatas, Local, Map, Operand, Place, Rvalue, Set,
    StatementKind, TerminatorKind, TyKind,
};
use crate::util::{enumerate_bbds, get_terminator, BB0};

pub fn get_ghosts(bbd0: &BasicBlockData, n_args: usize) -> Set<Local> {
    let mut ghosts: Set<Local> = Set::new();
    for stmt in &bbd0.statements {
        if let StatementKind::Assign(box (
            Place { local, .. },
            Rvalue::Use(Operand::Constant(constant)),
        )) = &stmt.kind
        {
            if let TyKind::Bool = &constant.literal.ty().kind() {
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
    pub bbds: &'a BasicBlockDatas<'tcx>,
    /// ghosts are locals that are generated by rustc, and are not part of the original program
    pub ghosts: &'a Set<Local>,
}
impl<'tcx> Index<BasicBlock> for Basic<'_, 'tcx> {
    type Output = BasicBlockData<'tcx>;
    fn index(&self, bb: BasicBlock) -> &Self::Output { &self.bbds[bb] }
}

impl<'a, 'tcx> Basic<'a, 'tcx> {
    pub fn is_ghost_switching(self, bb: BasicBlock) -> bool {
        if let TerminatorKind::SwitchInt {
            targets,
            discr: Operand::Copy(Place { local, .. }),
            ..
        } = &get_terminator(&self[bb]).kind
        {
            if self.ghosts.contains(local) {
                assert!(targets.all_targets().len() == 2);
                return true;
            }
        }
        false
    }
    pub fn is_panicking(self, bb: BasicBlock) -> bool {
        matches!(
            &get_terminator(&self[bb]).kind,
            TerminatorKind::Call { destination: None, .. }
                | TerminatorKind::Abort
                | TerminatorKind::Unreachable
        )
    }
    pub fn get_targets(self, bb: BasicBlock) -> Vec<BasicBlock> {
        let terminator = get_terminator(&self[bb]);
        match &terminator.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. } => {
                vec![*target]
            }
            TerminatorKind::Unreachable
            | TerminatorKind::Return
            | TerminatorKind::Call { destination: None, .. } => vec![],
            TerminatorKind::SwitchInt { targets, .. } => {
                let targets = targets.all_targets();
                if self.is_ghost_switching(bb) {
                    vec![targets[0]]
                } else {
                    targets.to_vec()
                }
            }
            TerminatorKind::Call { destination: Some((_, target)), .. } => vec![*target],
            _ => panic!("unsupported terminator {:?}", terminator),
        }
    }

    pub fn get_switches(self) -> Vec<BasicBlock> {
        let mut switches = Vec::<BasicBlock>::new();
        for (bb, bbd) in enumerate_bbds(self.bbds) {
            let terminator = get_terminator(bbd);
            match &terminator.kind {
                TerminatorKind::Goto { .. }
                | TerminatorKind::Drop { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Unreachable
                | TerminatorKind::Return
                | TerminatorKind::Call { .. } => {}
                TerminatorKind::SwitchInt { .. } => {
                    switches.push(bb);
                }
                _ => panic!("unsupported terminator {:?}", terminator),
            }
        }
        switches.sort_unstable();
        switches
    }

    pub fn get_ins_outs_map(
        self,
        n_init_ins: usize,
    ) -> (Map<BasicBlock, Set<Local>>, Map<BasicBlock, Set<Local>>) {
        fn dfs(
            me: BasicBlock,
            ins: &Set<Local>,
            discr_local: Option<Local>,
            basic: Basic,
            ins_map: &mut Map<BasicBlock, Set<Local>>,
        ) {
            let mut ins = ins.clone();
            /* shrink */
            if basic.is_panicking(me) {
                ins.clear();
            }
            for stmt in &basic[me].statements {
                if let StatementKind::StorageDead(local) = &stmt.kind {
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
                }
                ins.retain(|local| ins_ex.contains(local));
            }
            /* calc */
            ins_map.insert(me, ins.clone());
            for stmt in &basic[me].statements {
                match &stmt.kind {
                    StatementKind::Assign(box (Place { local, .. }, _))
                        if basic.ghosts.contains(local) => {}
                    StatementKind::Assign(box (_, Rvalue::Discriminant(_)))
                    | StatementKind::StorageLive(_) => {}
                    StatementKind::Assign(box (Place { local, .. }, _))
                    | StatementKind::SetDiscriminant { place: box Place { local, .. }, .. } => {
                        ins.insert(*local);
                    }
                    StatementKind::StorageDead(local) => {
                        ins.remove(local);
                    }
                    _ => panic!("unsupported statement {:?}", stmt),
                }
            }
            let terminator = get_terminator(&basic[me]);
            let mut discr_local = None::<Local>;
            match &terminator.kind {
                TerminatorKind::Goto { .. }
                | TerminatorKind::Return
                | TerminatorKind::Drop { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Unreachable => {}

                TerminatorKind::SwitchInt { discr, .. } => match discr {
                    Operand::Copy(place) | Operand::Move(place) => discr_local = Some(place.local),
                    Operand::Constant(..) => panic!("unexpected discriminant {:?}", discr),
                },
                TerminatorKind::Call { destination, .. } => {
                    if let Some((Place { local, .. }, _)) = destination {
                        ins.insert(*local);
                    }
                }
                _ => panic!("unsupported terminator {:?}", terminator),
            }
            for him in basic.get_targets(me) {
                dfs(him, &ins, discr_local, basic, ins_map);
            }
        } // fn dfs
        let mut ins_map = Map::<BasicBlock, Set<Local>>::new();

        let mut init_ins: Set<Local> = Set::new();
        for i in 1..=n_init_ins {
            init_ins.insert(Local::from(i));
        }
        dfs(BB0, &init_ins, None, self, &mut ins_map);
        let mut outs_map = Map::<BasicBlock, Set<Local>>::new();
        for (me, _) in enumerate_bbds(self.bbds) {
            let mut outs = Set::<Local>::new();
            for him in self.get_targets(me) {
                outs.extend(ins_map[&him].clone());
            }
            outs_map.insert(me, outs);
        }
        (ins_map, outs_map)
    }
}
