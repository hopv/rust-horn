(set-info :original "10-trees/trees-4-inc-some2-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_tree@_sm3 ((Array Int Int) Int ))
(declare-rel nd_tree@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_tree (Bool Bool Bool (Array Int Int) Int ))
(declare-rel sum@_sm ((Array Int Int) Int ))
(declare-rel sum@tailrecurse ((Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel sum@tailrecurse._crit_edge.split ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel sum (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@empty.loop (Int (Array Int Int) Int Int Int Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int Int Int ))
(declare-rel main@tailrecurse.i2 (Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@take_some_rest.exit5.split ())
(declare-var nd_tree@%_6_0 Int )
(declare-var nd_tree@%sh_0 (Array Int Int) )
(declare-var nd_tree@%_8_0 Int )
(declare-var nd_tree@%_9_0 Int )
(declare-var nd_tree@%_sm_0 Int )
(declare-var nd_tree@%sm_0 (Array Int Int) )
(declare-var nd_tree@%sh1_0 (Array Int Int) )
(declare-var nd_tree@%_11_0 Int )
(declare-var nd_tree@%_12_0 Int )
(declare-var nd_tree@%_sm2_0 Int )
(declare-var nd_tree@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_2 Int )
(declare-var nd_tree@%_2_0 Int )
(declare-var @nd_0 Int )
(declare-var nd_tree@%_3_0 Int )
(declare-var nd_tree@%_br_0 Bool )
(declare-var nd_tree@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_0 Int )
(declare-var nd_tree@%sm3_0 (Array Int Int) )
(declare-var nd_tree@_sm3_0 Bool )
(declare-var nd_tree@_br4_0 Bool )
(declare-var nd_tree@_call_0 Bool )
(declare-var nd_tree@%_sh_0 Int )
(declare-var nd_tree@%sm2_0 (Array Int Int) )
(declare-var nd_tree@UnifiedReturnBlock_0 Bool )
(declare-var nd_tree@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_1 Int )
(declare-var nd_tree@UnifiedReturnBlock.split_0 Bool )
(declare-var sum@%_call_0 Int )
(declare-var sum@%_sh_0 Int )
(declare-var sum@%_6_0 Int )
(declare-var sum@%_call1_0 Int )
(declare-var sum@%_8_0 Int )
(declare-var sum@%_call2_0 Int )
(declare-var sum@%_11_0 Int )
(declare-var sum@%_br3_0 Bool )
(declare-var sum@%_br_0 Bool )
(declare-var sum@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var sum@%.tr3_2 Int )
(declare-var sum@%accumulator.tr2_2 Int )
(declare-var sum@%sm_0 (Array Int Int) )
(declare-var sum@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var sum@arg.0_0 Int )
(declare-var sum@%accumulator.tr.lcssa_0 Int )
(declare-var sum@_sm_0 Bool )
(declare-var sum@tailrecurse_0 Bool )
(declare-var sum@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var sum@%.tr3_0 Int )
(declare-var sum@%accumulator.tr2_0 Int )
(declare-var sum@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var sum@%.tr3_1 Int )
(declare-var sum@%accumulator.tr2_1 Int )
(declare-var sum@tailrecurse._crit_edge_0 Bool )
(declare-var sum@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var sum@%accumulator.tr.lcssa_1 Int )
(declare-var sum@tailrecurse._crit_edge.split_0 Bool )
(declare-var sum@%sh_0 (Array Int Int) )
(declare-var sum@%_10_0 Int )
(declare-var sum@%_tail_0 Int )
(declare-var sum@tailrecurse_1 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%_53_0 Int )
(declare-var main@%_50_0 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Bool )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_40_0 Int )
(declare-var main@%_41_0 Int )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%sh4_0 (Array Int Int) )
(declare-var main@%_42_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Bool )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%_30_0 Bool )
(declare-var main@%.tr1.i1.be_3 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%.tr1.i1.ph_2 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%.tr1.i.be_3 Int )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%sh2_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%.tr1.i_0 Int )
(declare-var main@%.tr1.i_1 Int )
(declare-var main@_5_0 Bool )
(declare-var main@_20_0 Bool )
(declare-var main@_24_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@_27_0 Bool )
(declare-var main@%_29_0 Int )
(declare-var main@tailrecurse.i.backedge_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)| Bool )
(declare-var main@%.tr1.i.be_0 Int )
(declare-var main@%.tr1.i.be_1 Int )
(declare-var main@%.tr1.i.be_2 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%.tr1.i_2 Int )
(declare-var main@_9_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@_14_0 Bool )
(declare-var main@%_16_0 Int )
(declare-var main@_17_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@tailrecurse.i2.preheader_0 Bool )
(declare-var main@%.tr1.i1.ph_0 Int )
(declare-var main@%.tr1.i1.ph_1 Int )
(declare-var main@tailrecurse.i2_0 Bool )
(declare-var main@%.tr1.i1_0 Int )
(declare-var main@%.tr1.i1_1 Int )
(declare-var main@_31_0 Bool )
(declare-var main@_45_0 Bool )
(declare-var main@_49_0 Bool )
(declare-var main@%_51_0 Int )
(declare-var main@_52_0 Bool )
(declare-var main@%_54_0 Int )
(declare-var main@tailrecurse.i2.backedge_0 Bool )
(declare-var |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)| Bool )
(declare-var main@%.tr1.i1.be_0 Int )
(declare-var main@%.tr1.i1.be_1 Int )
(declare-var main@%.tr1.i1.be_2 Int )
(declare-var main@tailrecurse.i2_1 Bool )
(declare-var main@%.tr1.i1_2 Int )
(declare-var main@take_some_rest.exit5_0 Bool )
(declare-var main@take_some_rest.exit5.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (nd_tree true true true nd_tree@%shadow.mem.0.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree false true true nd_tree@%shadow.mem.0.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree false false false nd_tree@%shadow.mem.0.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree@_sm3 nd_tree@%sm3_0 @nd_0))
(rule (let ((a!1 (=> nd_tree@_call_0 (= nd_tree@%_9_0 (+ nd_tree@%_6_0 (* 4 1)))))
      (a!2 (=> nd_tree@_call_0 (= nd_tree@%_12_0 (+ nd_tree@%_6_0 (* 8 1))))))
(let ((a!3 (and (nd_tree@_sm3 nd_tree@%sm3_0 @nd_0)
                true
                (= nd_tree@%_2_0 @nd_0)
                (= nd_tree@%_br_0 (= nd_tree@%_3_0 0))
                (=> nd_tree@_br4_0 (and nd_tree@_br4_0 nd_tree@_sm3_0))
                (=> (and nd_tree@_br4_0 nd_tree@_sm3_0) (not nd_tree@%_br_0))
                (=> nd_tree@_call_0 (and nd_tree@_call_0 nd_tree@_sm3_0))
                (=> (and nd_tree@_call_0 nd_tree@_sm3_0) nd_tree@%_br_0)
                (=> nd_tree@_call_0 (= nd_tree@%_sh_0 nd_tree@%_6_0))
                (nd_tree nd_tree@_call_0
                         false
                         false
                         nd_tree@%sh_0
                         nd_tree@%_8_0)
                a!1
                (=> nd_tree@_call_0
                    (or (<= nd_tree@%_6_0 0) (> nd_tree@%_9_0 0)))
                (=> nd_tree@_call_0 (= nd_tree@%_sm_0 nd_tree@%_9_0))
                (=> nd_tree@_call_0 (> nd_tree@%_6_0 0))
                (=> nd_tree@_call_0
                    (= nd_tree@%sm_0
                       (store nd_tree@%sh_0 nd_tree@%_sm_0 nd_tree@%_8_0)))
                (nd_tree nd_tree@_call_0
                         false
                         false
                         nd_tree@%sh1_0
                         nd_tree@%_11_0)
                a!2
                (=> nd_tree@_call_0
                    (or (<= nd_tree@%_6_0 0) (> nd_tree@%_12_0 0)))
                (=> nd_tree@_call_0 (= nd_tree@%_sm2_0 nd_tree@%_12_0))
                (=> nd_tree@_call_0 (> nd_tree@%_6_0 0))
                (=> nd_tree@_call_0
                    (= nd_tree@%sm2_0
                       (store nd_tree@%sh1_0 nd_tree@%_sm2_0 nd_tree@%_11_0)))
                (=> nd_tree@UnifiedReturnBlock_0
                    (or (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br4_0)
                        (and nd_tree@UnifiedReturnBlock_0 nd_tree@_call_0)))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br4_0)
                    (= nd_tree@%shadow.mem.0.0_0 nd_tree@%sm3_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br4_0)
                    (= nd_tree@%UnifiedRetVal_0 0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_call_0)
                    (= nd_tree@%shadow.mem.0.0_1 nd_tree@%sm2_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_call_0)
                    (= nd_tree@%UnifiedRetVal_1 nd_tree@%_sh_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br4_0)
                    (= nd_tree@%shadow.mem.0.0_2 nd_tree@%shadow.mem.0.0_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br4_0)
                    (= nd_tree@%UnifiedRetVal_2 nd_tree@%UnifiedRetVal_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_call_0)
                    (= nd_tree@%shadow.mem.0.0_2 nd_tree@%shadow.mem.0.0_1))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_call_0)
                    (= nd_tree@%UnifiedRetVal_2 nd_tree@%UnifiedRetVal_1))
                (=> nd_tree@UnifiedReturnBlock.split_0
                    (and nd_tree@UnifiedReturnBlock.split_0
                         nd_tree@UnifiedReturnBlock_0))
                nd_tree@UnifiedReturnBlock.split_0)))
  (=> a!3
      (nd_tree@UnifiedReturnBlock.split
        nd_tree@%shadow.mem.0.0_2
        nd_tree@%UnifiedRetVal_2
        nd_tree@%sm3_0
        @nd_0)))))
(rule (=> (nd_tree@UnifiedReturnBlock.split
      nd_tree@%shadow.mem.0.0_0
      nd_tree@%UnifiedRetVal_0
      nd_tree@%sm3_0
      @nd_0)
    (nd_tree true
             false
             false
             nd_tree@%shadow.mem.0.0_0
             nd_tree@%UnifiedRetVal_0)))
(rule (sum true
     true
     true
     sum@%sm_0
     sum@%shadow.mem.0.1_0
     sum@arg.0_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum false
     true
     true
     sum@%sm_0
     sum@%shadow.mem.0.1_0
     sum@arg.0_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum false
     false
     false
     sum@%sm_0
     sum@%shadow.mem.0.1_0
     sum@arg.0_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum@_sm sum@%sm_0 sum@arg.0_0))
(rule (=> (and (sum@_sm sum@%sm_0 sum@arg.0_0)
         true
         (= sum@%_br_0 (= sum@arg.0_0 0))
         (=> sum@tailrecurse_0 (and sum@tailrecurse_0 sum@_sm_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0) (not sum@%_br_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0)
             (= sum@%shadow.mem.0.0_0 sum@%sm_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0) (= sum@%.tr3_0 sum@arg.0_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0) (= sum@%accumulator.tr2_0 0))
         (=> (and sum@tailrecurse_0 sum@_sm_0)
             (= sum@%shadow.mem.0.0_1 sum@%shadow.mem.0.0_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0) (= sum@%.tr3_1 sum@%.tr3_0))
         (=> (and sum@tailrecurse_0 sum@_sm_0)
             (= sum@%accumulator.tr2_1 sum@%accumulator.tr2_0))
         sum@tailrecurse_0)
    (sum@tailrecurse sum@%sm_0
                     sum@%.tr3_1
                     sum@%shadow.mem.0.0_1
                     sum@%accumulator.tr2_1
                     sum@arg.0_0)))
(rule (=> (and (sum@_sm sum@%sm_0 sum@arg.0_0)
         true
         (= sum@%_br_0 (= sum@arg.0_0 0))
         (=> sum@tailrecurse._crit_edge_0
             (and sum@tailrecurse._crit_edge_0 sum@_sm_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_sm_0) sum@%_br_0)
         (=> (and sum@tailrecurse._crit_edge_0 sum@_sm_0)
             (= sum@%shadow.mem.0.1_0 sum@%sm_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_sm_0)
             (= sum@%accumulator.tr.lcssa_0 0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_sm_0)
             (= sum@%shadow.mem.0.1_1 sum@%shadow.mem.0.1_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_sm_0)
             (= sum@%accumulator.tr.lcssa_1 sum@%accumulator.tr.lcssa_0))
         (=> sum@tailrecurse._crit_edge.split_0
             (and sum@tailrecurse._crit_edge.split_0
                  sum@tailrecurse._crit_edge_0))
         sum@tailrecurse._crit_edge.split_0)
    (sum@tailrecurse._crit_edge.split
      sum@%sm_0
      sum@%shadow.mem.0.1_1
      sum@%accumulator.tr.lcssa_1
      sum@arg.0_0)))
(rule (let ((a!1 (= sum@%_call_0 (+ (+ sum@%.tr3_0 (* 0 12)) 4)))
      (a!2 (= sum@%_call1_0 (+ (+ sum@%.tr3_0 (* 0 12)) 0)))
      (a!3 (= sum@%_call2_0 (+ (+ sum@%.tr3_0 (* 0 12)) 8))))
  (=> (and (sum@tailrecurse sum@%sm_0
                            sum@%.tr3_0
                            sum@%shadow.mem.0.0_0
                            sum@%accumulator.tr2_0
                            sum@arg.0_0)
           true
           a!1
           (or (<= sum@%.tr3_0 0) (> sum@%_call_0 0))
           (> sum@%.tr3_0 0)
           (= sum@%_sh_0 (select sum@%shadow.mem.0.0_0 sum@%_call_0))
           (sum true
                false
                false
                sum@%shadow.mem.0.0_0
                sum@%sh_0
                sum@%_sh_0
                sum@%_6_0)
           a!2
           (or (<= sum@%.tr3_0 0) (> sum@%_call1_0 0))
           (= sum@%_8_0 (select sum@%sh_0 sum@%_call1_0))
           a!3
           (or (<= sum@%.tr3_0 0) (> sum@%_call2_0 0))
           (> sum@%.tr3_0 0)
           (= sum@%_10_0 (select sum@%sh_0 sum@%_call2_0))
           (= sum@%_11_0 (+ sum@%_6_0 sum@%accumulator.tr2_0))
           (= sum@%_tail_0 (+ sum@%_11_0 sum@%_8_0))
           (= sum@%_br3_0 (= sum@%_10_0 0))
           (=> sum@tailrecurse_1 (and sum@tailrecurse_1 sum@tailrecurse_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0) (not sum@%_br3_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%shadow.mem.0.0_1 sum@%sh_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%.tr3_1 sum@%_10_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%accumulator.tr2_1 sum@%_tail_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%shadow.mem.0.0_2 sum@%shadow.mem.0.0_1))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%.tr3_2 sum@%.tr3_1))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%accumulator.tr2_2 sum@%accumulator.tr2_1))
           sum@tailrecurse_1)
      (sum@tailrecurse sum@%sm_0
                       sum@%.tr3_2
                       sum@%shadow.mem.0.0_2
                       sum@%accumulator.tr2_2
                       sum@arg.0_0))))
(rule (let ((a!1 (= sum@%_call_0 (+ (+ sum@%.tr3_0 (* 0 12)) 4)))
      (a!2 (= sum@%_call1_0 (+ (+ sum@%.tr3_0 (* 0 12)) 0)))
      (a!3 (= sum@%_call2_0 (+ (+ sum@%.tr3_0 (* 0 12)) 8))))
  (=> (and (sum@tailrecurse sum@%sm_0
                            sum@%.tr3_0
                            sum@%shadow.mem.0.0_0
                            sum@%accumulator.tr2_0
                            sum@arg.0_0)
           true
           a!1
           (or (<= sum@%.tr3_0 0) (> sum@%_call_0 0))
           (> sum@%.tr3_0 0)
           (= sum@%_sh_0 (select sum@%shadow.mem.0.0_0 sum@%_call_0))
           (sum true
                false
                false
                sum@%shadow.mem.0.0_0
                sum@%sh_0
                sum@%_sh_0
                sum@%_6_0)
           a!2
           (or (<= sum@%.tr3_0 0) (> sum@%_call1_0 0))
           (= sum@%_8_0 (select sum@%sh_0 sum@%_call1_0))
           a!3
           (or (<= sum@%.tr3_0 0) (> sum@%_call2_0 0))
           (> sum@%.tr3_0 0)
           (= sum@%_10_0 (select sum@%sh_0 sum@%_call2_0))
           (= sum@%_11_0 (+ sum@%_6_0 sum@%accumulator.tr2_0))
           (= sum@%_tail_0 (+ sum@%_11_0 sum@%_8_0))
           (= sum@%_br3_0 (= sum@%_10_0 0))
           (=> sum@tailrecurse._crit_edge_0
               (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0))
           (=> (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0) sum@%_br3_0)
           (=> (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0)
               (= sum@%shadow.mem.0.1_0 sum@%sh_0))
           (=> (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0)
               (= sum@%accumulator.tr.lcssa_0 sum@%_tail_0))
           (=> (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0)
               (= sum@%shadow.mem.0.1_1 sum@%shadow.mem.0.1_0))
           (=> (and sum@tailrecurse._crit_edge_0 sum@tailrecurse_0)
               (= sum@%accumulator.tr.lcssa_1 sum@%accumulator.tr.lcssa_0))
           (=> sum@tailrecurse._crit_edge.split_0
               (and sum@tailrecurse._crit_edge.split_0
                    sum@tailrecurse._crit_edge_0))
           sum@tailrecurse._crit_edge.split_0)
      (sum@tailrecurse._crit_edge.split
        sum@%sm_0
        sum@%shadow.mem.0.1_1
        sum@%accumulator.tr.lcssa_1
        sum@arg.0_0))))
(rule (=> (sum@tailrecurse._crit_edge.split
      sum@%sm_0
      sum@%shadow.mem.0.1_0
      sum@%accumulator.tr.lcssa_0
      sum@arg.0_0)
    (sum true
         false
         false
         sum@%sm_0
         sum@%shadow.mem.0.1_0
         sum@arg.0_0
         sum@%accumulator.tr.lcssa_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 0))
         main@%_1_0
         (nd_tree true false false main@%sh_0 main@%_2_0)
         (sum true false false main@%sh_0 main@%sh2_0 main@%_2_0 main@%_3_0)
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @nd_0
                     main@%sh2_0
                     main@%_2_0
                     main@%_3_0
                     main@%loop.bound_0
                     main@%loop.bound1_0)))
(rule (=> (and (main@empty.loop @nd_0
                          main@%sh2_0
                          main@%_2_0
                          main@%_3_0
                          main@%loop.bound_0
                          main@%loop.bound1_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop @nd_0
                     main@%sh2_0
                     main@%_2_0
                     main@%_3_0
                     main@%loop.bound_0
                     main@%loop.bound1_0)))
(rule (=> (and (main@empty.loop @nd_0
                          main@%sh2_0
                          main@%_2_0
                          main@%_3_0
                          main@%loop.bound_0
                          main@%loop.bound1_0)
         true
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@empty.loop_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (not main@%nd.loop.cond_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr1.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr1.i_1 main@%.tr1.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      @nd_0
      main@%.tr1.i_1
      main@%sh2_0
      main@%_2_0
      main@%_3_0
      main@%loop.bound_0
      main@%loop.bound1_0)))
(rule (let ((a!1 (= main@%_25_0 (+ (+ main@%.tr1.i_0 (* 0 12)) 4)))
      (a!2 (= main@%_28_0 (+ (+ main@%.tr1.i_0 (* 0 12)) 8))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%.tr1.i_0
                  main@%sh2_0
                  main@%_2_0
                  main@%_3_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_4_0 (= main@%.tr1.i_0 0))
                (=> main@_5_0 (and main@_5_0 main@tailrecurse.i_0))
                (=> (and main@_5_0 main@tailrecurse.i_0) (not main@%_4_0))
                (=> main@_5_0 (= main@%_6_0 @nd_0))
                (=> main@_5_0 (= main@%_8_0 (= main@%_7_0 main@%loop.bound1_0)))
                (=> main@_20_0 (and main@_20_0 main@_5_0))
                (=> (and main@_20_0 main@_5_0) main@%_8_0)
                (=> main@_20_0 (= main@%_21_0 @nd_0))
                (=> main@_20_0 (= main@%_23_0 (= main@%_22_0 0)))
                (=> main@_24_0 (and main@_24_0 main@_20_0))
                (=> (and main@_24_0 main@_20_0) (not main@%_23_0))
                (=> main@_24_0 a!1)
                (=> main@_24_0 (or (<= main@%.tr1.i_0 0) (> main@%_25_0 0)))
                (=> main@_24_0 (> main@%.tr1.i_0 0))
                (=> main@_24_0 (= main@%_26_0 (select main@%sh2_0 main@%_25_0)))
                (=> main@_27_0 (and main@_27_0 main@_20_0))
                (=> (and main@_27_0 main@_20_0) main@%_23_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= main@%.tr1.i_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> main@%.tr1.i_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sh2_0 main@%_28_0)))
                (=> |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)|
                    main@tailrecurse.i_0)
                (=> main@tailrecurse.i.backedge_0
                    (or (and main@tailrecurse.i.backedge_0 main@_27_0)
                        (and main@tailrecurse.i.backedge_0 main@_24_0)
                        |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)|
                    main@%_4_0)
                (=> (and main@tailrecurse.i.backedge_0 main@_27_0)
                    (= main@%.tr1.i.be_0 main@%_29_0))
                (=> (and main@tailrecurse.i.backedge_0 main@_24_0)
                    (= main@%.tr1.i.be_1 main@%_26_0))
                (=> |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)|
                    (= main@%.tr1.i.be_2 0))
                (=> (and main@tailrecurse.i.backedge_0 main@_27_0)
                    (= main@%.tr1.i.be_3 main@%.tr1.i.be_0))
                (=> (and main@tailrecurse.i.backedge_0 main@_24_0)
                    (= main@%.tr1.i.be_3 main@%.tr1.i.be_1))
                (=> |tuple(main@tailrecurse.i_0, main@tailrecurse.i.backedge_0)|
                    (= main@%.tr1.i.be_3 main@%.tr1.i.be_2))
                (=> main@tailrecurse.i_1
                    (and main@tailrecurse.i_1 main@tailrecurse.i.backedge_0))
                (=> (and main@tailrecurse.i_1 main@tailrecurse.i.backedge_0)
                    (= main@%.tr1.i_1 main@%.tr1.i.be_3))
                (=> (and main@tailrecurse.i_1 main@tailrecurse.i.backedge_0)
                    (= main@%.tr1.i_2 main@%.tr1.i_1))
                main@tailrecurse.i_1)))
  (=> a!3
      (main@tailrecurse.i
        @nd_0
        main@%.tr1.i_2
        main@%sh2_0
        main@%_2_0
        main@%_3_0
        main@%loop.bound_0
        main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_10_0 (+ (+ main@%.tr1.i_0 (* 0 12)) 0)))
      (a!2 (= main@%_15_0 (+ (+ main@%.tr1.i_0 (* 0 12)) 4)))
      (a!3 (= main@%_18_0 (+ (+ main@%.tr1.i_0 (* 0 12)) 8))))
(let ((a!4 (and (main@tailrecurse.i
                  @nd_0
                  main@%.tr1.i_0
                  main@%sh2_0
                  main@%_2_0
                  main@%_3_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_4_0 (= main@%.tr1.i_0 0))
                (=> main@_5_0 (and main@_5_0 main@tailrecurse.i_0))
                (=> (and main@_5_0 main@tailrecurse.i_0) (not main@%_4_0))
                (=> main@_5_0 (= main@%_6_0 @nd_0))
                (=> main@_5_0 (= main@%_8_0 (= main@%_7_0 main@%loop.bound1_0)))
                (=> main@_9_0 (and main@_9_0 main@_5_0))
                (=> (and main@_9_0 main@_5_0) (not main@%_8_0))
                (=> main@_9_0 a!1)
                (=> main@_9_0 (or (<= main@%.tr1.i_0 0) (> main@%_10_0 0)))
                (=> main@_9_0 (= main@%_11_0 @nd_0))
                (=> main@_9_0 (= main@%_13_0 (= main@%_12_0 0)))
                (=> main@_14_0 (and main@_14_0 main@_9_0))
                (=> (and main@_14_0 main@_9_0) (not main@%_13_0))
                (=> main@_14_0 a!2)
                (=> main@_14_0 (or (<= main@%.tr1.i_0 0) (> main@%_15_0 0)))
                (=> main@_14_0 (> main@%.tr1.i_0 0))
                (=> main@_14_0 (= main@%_16_0 (select main@%sh2_0 main@%_15_0)))
                (=> main@_17_0 (and main@_17_0 main@_9_0))
                (=> (and main@_17_0 main@_9_0) main@%_13_0)
                (=> main@_17_0 a!3)
                (=> main@_17_0 (or (<= main@%.tr1.i_0 0) (> main@%_18_0 0)))
                (=> main@_17_0 (> main@%.tr1.i_0 0))
                (=> main@_17_0 (= main@%_19_0 (select main@%sh2_0 main@%_18_0)))
                (=> main@tailrecurse.i2.preheader_0
                    (or (and main@tailrecurse.i2.preheader_0 main@_14_0)
                        (and main@tailrecurse.i2.preheader_0 main@_17_0)))
                (=> (and main@tailrecurse.i2.preheader_0 main@_14_0)
                    (= main@%.tr1.i1.ph_0 main@%_16_0))
                (=> (and main@tailrecurse.i2.preheader_0 main@_17_0)
                    (= main@%.tr1.i1.ph_1 main@%_19_0))
                (=> (and main@tailrecurse.i2.preheader_0 main@_14_0)
                    (= main@%.tr1.i1.ph_2 main@%.tr1.i1.ph_0))
                (=> (and main@tailrecurse.i2.preheader_0 main@_17_0)
                    (= main@%.tr1.i1.ph_2 main@%.tr1.i1.ph_1))
                (=> main@tailrecurse.i2_0
                    (and main@tailrecurse.i2_0 main@tailrecurse.i2.preheader_0))
                (=> (and main@tailrecurse.i2_0 main@tailrecurse.i2.preheader_0)
                    (= main@%.tr1.i1_0 main@%.tr1.i1.ph_2))
                (=> (and main@tailrecurse.i2_0 main@tailrecurse.i2.preheader_0)
                    (= main@%.tr1.i1_1 main@%.tr1.i1_0))
                main@tailrecurse.i2_0)))
  (=> a!4
      (main@tailrecurse.i2
        @nd_0
        main@%sh2_0
        main@%.tr1.i1_1
        main@%_10_0
        main@%_2_0
        main@%_3_0
        main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_50_0 (+ (+ main@%.tr1.i1_0 (* 0 12)) 4)))
      (a!2 (= main@%_53_0 (+ (+ main@%.tr1.i1_0 (* 0 12)) 8))))
(let ((a!3 (and (main@tailrecurse.i2
                  @nd_0
                  main@%sh2_0
                  main@%.tr1.i1_0
                  main@%_10_0
                  main@%_2_0
                  main@%_3_0
                  main@%loop.bound_0)
                true
                (= main@%_30_0 (= main@%.tr1.i1_0 0))
                (=> main@_31_0 (and main@_31_0 main@tailrecurse.i2_0))
                (=> (and main@_31_0 main@tailrecurse.i2_0) (not main@%_30_0))
                (=> main@_31_0 (= main@%_32_0 @nd_0))
                (=> main@_31_0
                    (= main@%_34_0 (= main@%_33_0 main@%loop.bound_0)))
                (=> main@_45_0 (and main@_45_0 main@_31_0))
                (=> (and main@_45_0 main@_31_0) main@%_34_0)
                (=> main@_45_0 (= main@%_46_0 @nd_0))
                (=> main@_45_0 (= main@%_48_0 (= main@%_47_0 0)))
                (=> main@_49_0 (and main@_49_0 main@_45_0))
                (=> (and main@_49_0 main@_45_0) (not main@%_48_0))
                (=> main@_49_0 a!1)
                (=> main@_49_0 (or (<= main@%.tr1.i1_0 0) (> main@%_50_0 0)))
                (=> main@_49_0 (> main@%.tr1.i1_0 0))
                (=> main@_49_0 (= main@%_51_0 (select main@%sh2_0 main@%_50_0)))
                (=> main@_52_0 (and main@_52_0 main@_45_0))
                (=> (and main@_52_0 main@_45_0) main@%_48_0)
                (=> main@_52_0 a!2)
                (=> main@_52_0 (or (<= main@%.tr1.i1_0 0) (> main@%_53_0 0)))
                (=> main@_52_0 (> main@%.tr1.i1_0 0))
                (=> main@_52_0 (= main@%_54_0 (select main@%sh2_0 main@%_53_0)))
                (=> |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)|
                    main@tailrecurse.i2_0)
                (=> main@tailrecurse.i2.backedge_0
                    (or (and main@tailrecurse.i2.backedge_0 main@_52_0)
                        (and main@tailrecurse.i2.backedge_0 main@_49_0)
                        |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)|))
                (=> |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)|
                    main@%_30_0)
                (=> (and main@tailrecurse.i2.backedge_0 main@_52_0)
                    (= main@%.tr1.i1.be_0 main@%_54_0))
                (=> (and main@tailrecurse.i2.backedge_0 main@_49_0)
                    (= main@%.tr1.i1.be_1 main@%_51_0))
                (=> |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)|
                    (= main@%.tr1.i1.be_2 0))
                (=> (and main@tailrecurse.i2.backedge_0 main@_52_0)
                    (= main@%.tr1.i1.be_3 main@%.tr1.i1.be_0))
                (=> (and main@tailrecurse.i2.backedge_0 main@_49_0)
                    (= main@%.tr1.i1.be_3 main@%.tr1.i1.be_1))
                (=> |tuple(main@tailrecurse.i2_0, main@tailrecurse.i2.backedge_0)|
                    (= main@%.tr1.i1.be_3 main@%.tr1.i1.be_2))
                (=> main@tailrecurse.i2_1
                    (and main@tailrecurse.i2_1 main@tailrecurse.i2.backedge_0))
                (=> (and main@tailrecurse.i2_1 main@tailrecurse.i2.backedge_0)
                    (= main@%.tr1.i1_1 main@%.tr1.i1.be_3))
                (=> (and main@tailrecurse.i2_1 main@tailrecurse.i2.backedge_0)
                    (= main@%.tr1.i1_2 main@%.tr1.i1_1))
                main@tailrecurse.i2_1)))
  (=> a!3
      (main@tailrecurse.i2
        @nd_0
        main@%sh2_0
        main@%.tr1.i1_2
        main@%_10_0
        main@%_2_0
        main@%_3_0
        main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@take_some_rest.exit5_0
               (= main@%_35_0 (+ main@%.tr1.i1_0 (* 0 12) 0)))))
(let ((a!2 (and (main@tailrecurse.i2
                  @nd_0
                  main@%sh2_0
                  main@%.tr1.i1_0
                  main@%_10_0
                  main@%_2_0
                  main@%_3_0
                  main@%loop.bound_0)
                true
                (= main@%_30_0 (= main@%.tr1.i1_0 0))
                (=> main@_31_0 (and main@_31_0 main@tailrecurse.i2_0))
                (=> (and main@_31_0 main@tailrecurse.i2_0) (not main@%_30_0))
                (=> main@_31_0 (= main@%_32_0 @nd_0))
                (=> main@_31_0
                    (= main@%_34_0 (= main@%_33_0 main@%loop.bound_0)))
                (=> main@take_some_rest.exit5_0
                    (and main@take_some_rest.exit5_0 main@_31_0))
                (=> (and main@take_some_rest.exit5_0 main@_31_0)
                    (not main@%_34_0))
                a!1
                (=> main@take_some_rest.exit5_0
                    (or (<= main@%.tr1.i1_0 0) (> main@%_35_0 0)))
                (=> main@take_some_rest.exit5_0 (= main@%_36_0 @nd_0))
                (=> main@take_some_rest.exit5_0
                    (= main@%_38_0 (select main@%sh2_0 main@%_10_0)))
                (=> main@take_some_rest.exit5_0
                    (= main@%_39_0 (+ main@%_38_0 1)))
                (=> main@take_some_rest.exit5_0
                    (= main@%sm_0 (store main@%sh2_0 main@%_10_0 main@%_39_0)))
                (=> main@take_some_rest.exit5_0
                    (= main@%_40_0 (select main@%sm_0 main@%_35_0)))
                (=> main@take_some_rest.exit5_0
                    (= main@%_41_0 (+ main@%_40_0 1)))
                (=> main@take_some_rest.exit5_0
                    (= main@%sm3_0 (store main@%sm_0 main@%_35_0 main@%_41_0)))
                (sum main@take_some_rest.exit5_0
                     false
                     false
                     main@%sm3_0
                     main@%sh4_0
                     main@%_2_0
                     main@%_42_0)
                (=> main@take_some_rest.exit5_0
                    (= main@%_43_0 (+ main@%_3_0 2)))
                (=> main@take_some_rest.exit5_0
                    (= main@%_44_0 (> main@%_42_0 main@%_43_0)))
                (=> main@take_some_rest.exit5_0 (not main@%_44_0))
                (=> main@take_some_rest.exit5.split_0
                    (and main@take_some_rest.exit5.split_0
                         main@take_some_rest.exit5_0))
                main@take_some_rest.exit5.split_0)))
  (=> a!2 main@take_some_rest.exit5.split))))
(query main@take_some_rest.exit5.split)

