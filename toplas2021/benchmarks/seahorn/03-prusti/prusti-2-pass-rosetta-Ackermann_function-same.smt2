(set-info :original "03-prusti/prusti-2-pass-rosetta-Ackermann_function-same.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel ack@_loop.bound (Int Int ))
(declare-rel ack@.lr.ph (Int Int Int Int Int ))
(declare-rel ack@tailrecurse._crit_edge.split (Int Int Int ))
(declare-rel ack (Bool Bool Bool Int Int Int ))
(declare-rel ack1@_loop.bound (Int Int ))
(declare-rel ack1@.lr.ph (Int Int Int Int Int ))
(declare-rel ack1@tailrecurse._crit_edge.split (Int Int Int ))
(declare-rel ack1 (Bool Bool Bool Int Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@entry.split ())
(declare-var ack@%_br4_0 Bool )
(declare-var ack@%_10_0 Int )
(declare-var ack@%_7_0 Bool )
(declare-var ack@%_call_0 Bool )
(declare-var ack@%_br_0 Bool )
(declare-var ack@%.tr4_2 Int )
(declare-var ack@arg.0_0 Int )
(declare-var ack@arg.1_0 Int )
(declare-var ack@%_br1_0 Int )
(declare-var ack@_loop.bound_0 Bool )
(declare-var ack@%loop.bound_0 Int )
(declare-var ack@.lr.ph_0 Bool )
(declare-var ack@%.tr35_0 Int )
(declare-var ack@%.tr4_0 Int )
(declare-var ack@%.tr35_1 Int )
(declare-var ack@%.tr4_1 Int )
(declare-var ack@tailrecurse._crit_edge_0 Bool )
(declare-var ack@%.tr3.lcssa_0 Int )
(declare-var ack@%.tr3.lcssa_1 Int )
(declare-var ack@tailrecurse._crit_edge.split_0 Bool )
(declare-var ack@%_br2_0 Int )
(declare-var ack@_9_0 Bool )
(declare-var ack@%_br3_0 Int )
(declare-var ack@tailrecurse.backedge_0 Bool )
(declare-var |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)| Bool )
(declare-var ack@%.tr3.be_0 Int )
(declare-var ack@%.tr3.be_1 Int )
(declare-var ack@%.tr3.be_2 Int )
(declare-var ack@.lr.ph_1 Bool )
(declare-var ack@%.tr35_2 Int )
(declare-var ack1@%_br4_0 Bool )
(declare-var ack1@%_10_0 Int )
(declare-var ack1@%_7_0 Bool )
(declare-var ack1@%_call_0 Bool )
(declare-var ack1@%_br_0 Bool )
(declare-var ack1@%.tr4_2 Int )
(declare-var ack1@arg.0_0 Int )
(declare-var ack1@arg.1_0 Int )
(declare-var ack1@%_br1_0 Int )
(declare-var ack1@_loop.bound_0 Bool )
(declare-var ack1@%loop.bound_0 Int )
(declare-var ack1@.lr.ph_0 Bool )
(declare-var ack1@%.tr35_0 Int )
(declare-var ack1@%.tr4_0 Int )
(declare-var ack1@%.tr35_1 Int )
(declare-var ack1@%.tr4_1 Int )
(declare-var ack1@tailrecurse._crit_edge_0 Bool )
(declare-var ack1@%.tr3.lcssa_0 Int )
(declare-var ack1@%.tr3.lcssa_1 Int )
(declare-var ack1@tailrecurse._crit_edge.split_0 Bool )
(declare-var ack1@%_br2_0 Int )
(declare-var ack1@_9_0 Bool )
(declare-var ack1@%_br3_0 Int )
(declare-var ack1@tailrecurse.backedge_0 Bool )
(declare-var |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)| Bool )
(declare-var ack1@%.tr3.be_0 Int )
(declare-var ack1@%.tr3.be_1 Int )
(declare-var ack1@%.tr3.be_2 Int )
(declare-var ack1@.lr.ph_1 Bool )
(declare-var ack1@%.tr35_2 Int )
(declare-var main@%_0_0 Int )
(declare-var @nd_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@entry.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (ack true true true ack@arg.0_0 ack@arg.1_0 ack@%_br1_0))
(rule (ack false true true ack@arg.0_0 ack@arg.1_0 ack@%_br1_0))
(rule (ack false false false ack@arg.0_0 ack@arg.1_0 ack@%_br1_0))
(rule (ack@_loop.bound ack@arg.0_0 ack@arg.1_0))
(rule (=> (and (ack@_loop.bound ack@arg.0_0 ack@arg.1_0)
         true
         (= ack@%_call_0 (= ack@%loop.bound_0 0))
         ack@%_call_0
         (= ack@%_br_0 (= ack@arg.0_0 0))
         (=> ack@.lr.ph_0 (and ack@.lr.ph_0 ack@_loop.bound_0))
         (=> (and ack@.lr.ph_0 ack@_loop.bound_0) (not ack@%_br_0))
         (=> (and ack@.lr.ph_0 ack@_loop.bound_0) (= ack@%.tr35_0 ack@arg.1_0))
         (=> (and ack@.lr.ph_0 ack@_loop.bound_0) (= ack@%.tr4_0 ack@arg.0_0))
         (=> (and ack@.lr.ph_0 ack@_loop.bound_0) (= ack@%.tr35_1 ack@%.tr35_0))
         (=> (and ack@.lr.ph_0 ack@_loop.bound_0) (= ack@%.tr4_1 ack@%.tr4_0))
         ack@.lr.ph_0)
    (ack@.lr.ph ack@%loop.bound_0
                ack@%.tr35_1
                ack@%.tr4_1
                ack@arg.0_0
                ack@arg.1_0)))
(rule (let ((a!1 (and (ack@_loop.bound ack@arg.0_0 ack@arg.1_0)
                true
                (= ack@%_call_0 (= ack@%loop.bound_0 0))
                ack@%_call_0
                (= ack@%_br_0 (= ack@arg.0_0 0))
                (=> ack@tailrecurse._crit_edge_0
                    (and ack@tailrecurse._crit_edge_0 ack@_loop.bound_0))
                (=> (and ack@tailrecurse._crit_edge_0 ack@_loop.bound_0)
                    ack@%_br_0)
                (=> (and ack@tailrecurse._crit_edge_0 ack@_loop.bound_0)
                    (= ack@%.tr3.lcssa_0 ack@arg.1_0))
                (=> (and ack@tailrecurse._crit_edge_0 ack@_loop.bound_0)
                    (= ack@%.tr3.lcssa_1 ack@%.tr3.lcssa_0))
                (=> ack@tailrecurse._crit_edge_0
                    (= ack@%_br1_0 (+ ack@%.tr3.lcssa_1 1)))
                (=> ack@tailrecurse._crit_edge.split_0
                    (and ack@tailrecurse._crit_edge.split_0
                         ack@tailrecurse._crit_edge_0))
                ack@tailrecurse._crit_edge.split_0)))
  (=> a!1
      (ack@tailrecurse._crit_edge.split ack@%_br1_0 ack@arg.0_0 ack@arg.1_0))))
(rule (let ((a!1 (and (ack@.lr.ph ack@%loop.bound_0
                            ack@%.tr35_0
                            ack@%.tr4_0
                            ack@arg.0_0
                            ack@arg.1_0)
                true
                (= ack@%_7_0 (= ack@%.tr35_0 0))
                (= ack@%_br2_0 (+ ack@%.tr4_0 (- 1)))
                (=> ack@_9_0 (and ack@_9_0 ack@.lr.ph_0))
                (=> (and ack@_9_0 ack@.lr.ph_0) (not ack@%_7_0))
                (=> ack@_9_0 (= ack@%_10_0 (+ ack@%.tr35_0 (- 1))))
                (ack ack@_9_0 false false ack@%.tr4_0 ack@%_10_0 ack@%_br3_0)
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    ack@.lr.ph_0)
                (=> ack@tailrecurse.backedge_0
                    (or (and ack@tailrecurse.backedge_0 ack@_9_0)
                        |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)| ack@%_7_0)
                (=> (and ack@tailrecurse.backedge_0 ack@_9_0)
                    (= ack@%.tr3.be_0 ack@%_br3_0))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    (= ack@%.tr3.be_1 1))
                (=> (and ack@tailrecurse.backedge_0 ack@_9_0)
                    (= ack@%.tr3.be_2 ack@%.tr3.be_0))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    (= ack@%.tr3.be_2 ack@%.tr3.be_1))
                (=> ack@tailrecurse.backedge_0
                    (= ack@%_br4_0 (= ack@%_br2_0 ack@%loop.bound_0)))
                (=> ack@.lr.ph_1 (and ack@.lr.ph_1 ack@tailrecurse.backedge_0))
                (=> (and ack@.lr.ph_1 ack@tailrecurse.backedge_0)
                    (not ack@%_br4_0))
                (=> (and ack@.lr.ph_1 ack@tailrecurse.backedge_0)
                    (= ack@%.tr35_1 ack@%.tr3.be_2))
                (=> (and ack@.lr.ph_1 ack@tailrecurse.backedge_0)
                    (= ack@%.tr4_1 ack@%_br2_0))
                (=> (and ack@.lr.ph_1 ack@tailrecurse.backedge_0)
                    (= ack@%.tr35_2 ack@%.tr35_1))
                (=> (and ack@.lr.ph_1 ack@tailrecurse.backedge_0)
                    (= ack@%.tr4_2 ack@%.tr4_1))
                ack@.lr.ph_1)))
  (=> a!1
      (ack@.lr.ph ack@%loop.bound_0
                  ack@%.tr35_2
                  ack@%.tr4_2
                  ack@arg.0_0
                  ack@arg.1_0))))
(rule (let ((a!1 (and (ack@.lr.ph ack@%loop.bound_0
                            ack@%.tr35_0
                            ack@%.tr4_0
                            ack@arg.0_0
                            ack@arg.1_0)
                true
                (= ack@%_7_0 (= ack@%.tr35_0 0))
                (= ack@%_br2_0 (+ ack@%.tr4_0 (- 1)))
                (=> ack@_9_0 (and ack@_9_0 ack@.lr.ph_0))
                (=> (and ack@_9_0 ack@.lr.ph_0) (not ack@%_7_0))
                (=> ack@_9_0 (= ack@%_10_0 (+ ack@%.tr35_0 (- 1))))
                (ack ack@_9_0 false false ack@%.tr4_0 ack@%_10_0 ack@%_br3_0)
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    ack@.lr.ph_0)
                (=> ack@tailrecurse.backedge_0
                    (or (and ack@tailrecurse.backedge_0 ack@_9_0)
                        |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)| ack@%_7_0)
                (=> (and ack@tailrecurse.backedge_0 ack@_9_0)
                    (= ack@%.tr3.be_0 ack@%_br3_0))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    (= ack@%.tr3.be_1 1))
                (=> (and ack@tailrecurse.backedge_0 ack@_9_0)
                    (= ack@%.tr3.be_2 ack@%.tr3.be_0))
                (=> |tuple(ack@.lr.ph_0, ack@tailrecurse.backedge_0)|
                    (= ack@%.tr3.be_2 ack@%.tr3.be_1))
                (=> ack@tailrecurse.backedge_0
                    (= ack@%_br4_0 (= ack@%_br2_0 ack@%loop.bound_0)))
                (=> ack@tailrecurse._crit_edge_0
                    (and ack@tailrecurse._crit_edge_0
                         ack@tailrecurse.backedge_0))
                (=> (and ack@tailrecurse._crit_edge_0
                         ack@tailrecurse.backedge_0)
                    ack@%_br4_0)
                (=> (and ack@tailrecurse._crit_edge_0
                         ack@tailrecurse.backedge_0)
                    (= ack@%.tr3.lcssa_0 ack@%.tr3.be_2))
                (=> (and ack@tailrecurse._crit_edge_0
                         ack@tailrecurse.backedge_0)
                    (= ack@%.tr3.lcssa_1 ack@%.tr3.lcssa_0))
                (=> ack@tailrecurse._crit_edge_0
                    (= ack@%_br1_0 (+ ack@%.tr3.lcssa_1 1)))
                (=> ack@tailrecurse._crit_edge.split_0
                    (and ack@tailrecurse._crit_edge.split_0
                         ack@tailrecurse._crit_edge_0))
                ack@tailrecurse._crit_edge.split_0)))
  (=> a!1
      (ack@tailrecurse._crit_edge.split ack@%_br1_0 ack@arg.0_0 ack@arg.1_0))))
(rule (=> (ack@tailrecurse._crit_edge.split ack@%_br1_0 ack@arg.0_0 ack@arg.1_0)
    (ack true false false ack@arg.0_0 ack@arg.1_0 ack@%_br1_0)))
(rule (ack1 true true true ack1@arg.0_0 ack1@arg.1_0 ack1@%_br1_0))
(rule (ack1 false true true ack1@arg.0_0 ack1@arg.1_0 ack1@%_br1_0))
(rule (ack1 false false false ack1@arg.0_0 ack1@arg.1_0 ack1@%_br1_0))
(rule (ack1@_loop.bound ack1@arg.0_0 ack1@arg.1_0))
(rule (=> (and (ack1@_loop.bound ack1@arg.0_0 ack1@arg.1_0)
         true
         (= ack1@%_call_0 (= ack1@%loop.bound_0 0))
         ack1@%_call_0
         (= ack1@%_br_0 (= ack1@arg.0_0 0))
         (=> ack1@.lr.ph_0 (and ack1@.lr.ph_0 ack1@_loop.bound_0))
         (=> (and ack1@.lr.ph_0 ack1@_loop.bound_0) (not ack1@%_br_0))
         (=> (and ack1@.lr.ph_0 ack1@_loop.bound_0)
             (= ack1@%.tr35_0 ack1@arg.1_0))
         (=> (and ack1@.lr.ph_0 ack1@_loop.bound_0)
             (= ack1@%.tr4_0 ack1@arg.0_0))
         (=> (and ack1@.lr.ph_0 ack1@_loop.bound_0)
             (= ack1@%.tr35_1 ack1@%.tr35_0))
         (=> (and ack1@.lr.ph_0 ack1@_loop.bound_0)
             (= ack1@%.tr4_1 ack1@%.tr4_0))
         ack1@.lr.ph_0)
    (ack1@.lr.ph ack1@%loop.bound_0
                 ack1@%.tr35_1
                 ack1@%.tr4_1
                 ack1@arg.0_0
                 ack1@arg.1_0)))
(rule (let ((a!1 (and (ack1@_loop.bound ack1@arg.0_0 ack1@arg.1_0)
                true
                (= ack1@%_call_0 (= ack1@%loop.bound_0 0))
                ack1@%_call_0
                (= ack1@%_br_0 (= ack1@arg.0_0 0))
                (=> ack1@tailrecurse._crit_edge_0
                    (and ack1@tailrecurse._crit_edge_0 ack1@_loop.bound_0))
                (=> (and ack1@tailrecurse._crit_edge_0 ack1@_loop.bound_0)
                    ack1@%_br_0)
                (=> (and ack1@tailrecurse._crit_edge_0 ack1@_loop.bound_0)
                    (= ack1@%.tr3.lcssa_0 ack1@arg.1_0))
                (=> (and ack1@tailrecurse._crit_edge_0 ack1@_loop.bound_0)
                    (= ack1@%.tr3.lcssa_1 ack1@%.tr3.lcssa_0))
                (=> ack1@tailrecurse._crit_edge_0
                    (= ack1@%_br1_0 (+ ack1@%.tr3.lcssa_1 1)))
                (=> ack1@tailrecurse._crit_edge.split_0
                    (and ack1@tailrecurse._crit_edge.split_0
                         ack1@tailrecurse._crit_edge_0))
                ack1@tailrecurse._crit_edge.split_0)))
  (=> a!1
      (ack1@tailrecurse._crit_edge.split ack1@%_br1_0 ack1@arg.0_0 ack1@arg.1_0))))
(rule (let ((a!1 (and (ack1@.lr.ph ack1@%loop.bound_0
                             ack1@%.tr35_0
                             ack1@%.tr4_0
                             ack1@arg.0_0
                             ack1@arg.1_0)
                true
                (= ack1@%_7_0 (= ack1@%.tr35_0 0))
                (= ack1@%_br2_0 (+ ack1@%.tr4_0 (- 1)))
                (=> ack1@_9_0 (and ack1@_9_0 ack1@.lr.ph_0))
                (=> (and ack1@_9_0 ack1@.lr.ph_0) (not ack1@%_7_0))
                (=> ack1@_9_0 (= ack1@%_10_0 (+ ack1@%.tr35_0 (- 1))))
                (ack1 ack1@_9_0
                      false
                      false
                      ack1@%.tr4_0
                      ack1@%_10_0
                      ack1@%_br3_0)
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    ack1@.lr.ph_0)
                (=> ack1@tailrecurse.backedge_0
                    (or (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                        |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    ack1@%_7_0)
                (=> (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                    (= ack1@%.tr3.be_0 ack1@%_br3_0))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    (= ack1@%.tr3.be_1 1))
                (=> (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                    (= ack1@%.tr3.be_2 ack1@%.tr3.be_0))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    (= ack1@%.tr3.be_2 ack1@%.tr3.be_1))
                (=> ack1@tailrecurse.backedge_0
                    (= ack1@%_br4_0 (= ack1@%_br2_0 ack1@%loop.bound_0)))
                (=> ack1@.lr.ph_1
                    (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0))
                (=> (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0)
                    (not ack1@%_br4_0))
                (=> (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr35_1 ack1@%.tr3.be_2))
                (=> (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr4_1 ack1@%_br2_0))
                (=> (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr35_2 ack1@%.tr35_1))
                (=> (and ack1@.lr.ph_1 ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr4_2 ack1@%.tr4_1))
                ack1@.lr.ph_1)))
  (=> a!1
      (ack1@.lr.ph ack1@%loop.bound_0
                   ack1@%.tr35_2
                   ack1@%.tr4_2
                   ack1@arg.0_0
                   ack1@arg.1_0))))
(rule (let ((a!1 (and (ack1@.lr.ph ack1@%loop.bound_0
                             ack1@%.tr35_0
                             ack1@%.tr4_0
                             ack1@arg.0_0
                             ack1@arg.1_0)
                true
                (= ack1@%_7_0 (= ack1@%.tr35_0 0))
                (= ack1@%_br2_0 (+ ack1@%.tr4_0 (- 1)))
                (=> ack1@_9_0 (and ack1@_9_0 ack1@.lr.ph_0))
                (=> (and ack1@_9_0 ack1@.lr.ph_0) (not ack1@%_7_0))
                (=> ack1@_9_0 (= ack1@%_10_0 (+ ack1@%.tr35_0 (- 1))))
                (ack1 ack1@_9_0
                      false
                      false
                      ack1@%.tr4_0
                      ack1@%_10_0
                      ack1@%_br3_0)
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    ack1@.lr.ph_0)
                (=> ack1@tailrecurse.backedge_0
                    (or (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                        |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    ack1@%_7_0)
                (=> (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                    (= ack1@%.tr3.be_0 ack1@%_br3_0))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    (= ack1@%.tr3.be_1 1))
                (=> (and ack1@tailrecurse.backedge_0 ack1@_9_0)
                    (= ack1@%.tr3.be_2 ack1@%.tr3.be_0))
                (=> |tuple(ack1@.lr.ph_0, ack1@tailrecurse.backedge_0)|
                    (= ack1@%.tr3.be_2 ack1@%.tr3.be_1))
                (=> ack1@tailrecurse.backedge_0
                    (= ack1@%_br4_0 (= ack1@%_br2_0 ack1@%loop.bound_0)))
                (=> ack1@tailrecurse._crit_edge_0
                    (and ack1@tailrecurse._crit_edge_0
                         ack1@tailrecurse.backedge_0))
                (=> (and ack1@tailrecurse._crit_edge_0
                         ack1@tailrecurse.backedge_0)
                    ack1@%_br4_0)
                (=> (and ack1@tailrecurse._crit_edge_0
                         ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr3.lcssa_0 ack1@%.tr3.be_2))
                (=> (and ack1@tailrecurse._crit_edge_0
                         ack1@tailrecurse.backedge_0)
                    (= ack1@%.tr3.lcssa_1 ack1@%.tr3.lcssa_0))
                (=> ack1@tailrecurse._crit_edge_0
                    (= ack1@%_br1_0 (+ ack1@%.tr3.lcssa_1 1)))
                (=> ack1@tailrecurse._crit_edge.split_0
                    (and ack1@tailrecurse._crit_edge.split_0
                         ack1@tailrecurse._crit_edge_0))
                ack1@tailrecurse._crit_edge.split_0)))
  (=> a!1
      (ack1@tailrecurse._crit_edge.split ack1@%_br1_0 ack1@arg.0_0 ack1@arg.1_0))))
(rule (=> (ack1@tailrecurse._crit_edge.split ack1@%_br1_0 ack1@arg.0_0 ack1@arg.1_0)
    (ack1 true false false ack1@arg.0_0 ack1@arg.1_0 ack1@%_br1_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (= main@%_0_0 @nd_0)
         (= main@%_2_0 @nd_0)
         (= main@%_4_0 (> main@%_1_0 (- 1)))
         (= main@%_5_0 (> main@%_3_0 (- 1)))
         (= main@%or.cond.i_0 (and main@%_4_0 main@%_5_0))
         main@%or.cond.i_0
         (ack true false false main@%_1_0 main@%_3_0 main@%_6_0)
         (ack1 true false false main@%_1_0 main@%_3_0 main@%_7_0)
         (= main@%_8_0 (= main@%_6_0 main@%_7_0))
         (not main@%_8_0)
         (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
         main@entry.split_0)
    main@entry.split))
(query main@entry.split)

