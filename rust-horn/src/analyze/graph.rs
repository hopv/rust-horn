use std::ops::Index;

use crate::types::{
    BasicBlock, BasicBlockData, BasicBlocks, Local, Map, Operand, OrderedSet, Place, Rvalue,
    StatementKind, TerminatorKind,
};
use crate::util::{enumerate_basicblock_datas, BB0};

#[derive(Copy, Clone)]
pub struct Basic<'a, 'tcx> {
    pub bbds: &'a BasicBlocks<'tcx>,
}
impl<'tcx> Index<BasicBlock> for Basic<'_, 'tcx> {
    type Output = BasicBlockData<'tcx>;
    fn index(&self, bb: BasicBlock) -> &Self::Output { &self.bbds[bb] }
}

impl<'a, 'tcx> Basic<'a, 'tcx> {
    pub fn is_panicking(self, bb: BasicBlock) -> bool {
        matches!(
            &self[bb].terminator().kind,
            TerminatorKind::Call { target: None, .. }
                | TerminatorKind::UnwindTerminate(..)
                | TerminatorKind::Unreachable
        )
    }
    pub fn get_targets(self, bb: BasicBlock) -> Vec<BasicBlock> {
        let terminator = self[bb].terminator();
        match &terminator.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            }
            | TerminatorKind::Assert { target, .. } => {
                vec![*target]
            }
            TerminatorKind::Unreachable
            | TerminatorKind::Return
            | TerminatorKind::Call { target: None, .. } => vec![],
            TerminatorKind::SwitchInt { targets, .. } => {
                let targets = targets.all_targets();
                targets.to_vec()
            }
            _ => panic!("unsupported terminator {:?}", terminator),
        }
    }

    pub fn get_switches(self) -> Vec<BasicBlock> {
        let mut switches = Vec::<BasicBlock>::new();
        for (bb, bbd) in enumerate_basicblock_datas(self.bbds) {
            let terminator = bbd.terminator();
            match &terminator.kind {
                TerminatorKind::Goto { .. }
                | TerminatorKind::Drop { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Unreachable
                | TerminatorKind::Return
                | TerminatorKind::FalseEdge { .. }
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
    ) -> (
        Map<BasicBlock, OrderedSet<Local>>,
        Map<BasicBlock, OrderedSet<Local>>,
    ) {
        fn dfs(
            me: BasicBlock,
            ins: &OrderedSet<Local>,
            discr_local: Option<Local>,
            basic: Basic,
            ins_map: &mut Map<BasicBlock, OrderedSet<Local>>,
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
                    StatementKind::Assign(box (_, Rvalue::Discriminant(_)))
                    | StatementKind::StorageLive(_) => {}
                    StatementKind::Assign(box (Place { local, .. }, _))
                    | StatementKind::SetDiscriminant {
                        place: box Place { local, .. },
                        ..
                    } => {
                        ins.insert(*local);
                    }
                    StatementKind::StorageDead(local) => {
                        ins.remove(local);
                    }
                    StatementKind::FakeRead(..) => {}
                    StatementKind::PlaceMention(..) => {}
                    _ => panic!("unsupported statement {:?}", stmt),
                }
            }
            let terminator = basic[me].terminator();
            let mut discr_local = None::<Local>;
            match &terminator.kind {
                TerminatorKind::Goto { .. }
                | TerminatorKind::Return
                | TerminatorKind::Drop { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Unreachable
                | TerminatorKind::FalseEdge { .. } => {}

                TerminatorKind::SwitchInt { discr, .. } => match discr {
                    Operand::Copy(place) | Operand::Move(place) => discr_local = Some(place.local),
                    Operand::Constant(..) => panic!("unexpected discriminant {:?}", discr),
                },
                TerminatorKind::Call {
                    destination,
                    target,
                    ..
                } => {
                    if target.is_some() {
                        ins.insert(destination.local);
                    }
                }
                _ => panic!("unsupported terminator {:?}", terminator),
            }
            for him in basic.get_targets(me) {
                dfs(him, &ins, discr_local, basic, ins_map);
            }
        } // fn dfs

        let mut ins_map = Map::<BasicBlock, OrderedSet<Local>>::new();

        let mut init_ins: OrderedSet<Local> = OrderedSet::new();
        for i in 1..=n_init_ins {
            init_ins.insert(Local::from(i));
        }
        dfs(BB0, &init_ins, None, self, &mut ins_map);
        let mut outs_map = Map::<BasicBlock, OrderedSet<Local>>::new();
        for (me, _) in enumerate_basicblock_datas(self.bbds) {
            let mut outs = OrderedSet::<Local>::new();
            for him in self.get_targets(me) {
                outs.extend(ins_map[&him].clone());
            }
            outs_map.insert(me, outs);
        }
        (ins_map, outs_map)
    }
}
