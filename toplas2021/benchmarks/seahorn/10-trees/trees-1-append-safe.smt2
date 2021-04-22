(set-info :original "10-trees/trees-1-append-safe.bc")
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
(declare-rel main@.lr.ph.i (Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@append.exit.split ())
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
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%.0.1_0 Int )
(declare-var main@%sh5_0 (Array Int Int) )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_1_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sh1_0 (Array Int Int) )
(declare-var main@%sh2_0 (Array Int Int) )
(declare-var main@%_5_0 Bool )
(declare-var main@%.tr2.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%sh3_0 (Array Int Int) )
(declare-var main@%_4_0 Int )
(declare-var main@.lr.ph.i_0 Bool )
(declare-var main@%.tr2.i_0 Int )
(declare-var main@%.tr2.i_1 Int )
(declare-var main@append.exit_0 Bool )
(declare-var main@%.tr.lcssa.i_0 Int )
(declare-var main@%.tr.lcssa.i_1 Int )
(declare-var main@append.exit.split_0 Bool )
(declare-var main@%.tr.be.i_0 Int )
(declare-var main@.lr.ph.i_1 Bool )
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
         (> main@%_0_0 0)
         (= main@%.0.sroa_cast_0 main@%_0_0)
         (nd_tree true false false main@%sh_0 main@%_1_0)
         (= main@%sm_0 (store main@%sh_0 main@%_0_0 main@%_1_0))
         (nd_tree true false false main@%sh1_0 main@%_2_0)
         (sum true false false main@%sh1_0 main@%sh2_0 main@%_1_0 main@%_3_0)
         (sum true false false main@%sh2_0 main@%sh3_0 main@%_2_0 main@%_4_0)
         (= main@%_5_0 (= main@%_1_0 0))
         (=> main@.lr.ph.i_0 (and main@.lr.ph.i_0 main@entry_0))
         (=> (and main@.lr.ph.i_0 main@entry_0) (not main@%_5_0))
         (=> (and main@.lr.ph.i_0 main@entry_0) (= main@%.tr2.i_0 main@%_0_0))
         (=> (and main@.lr.ph.i_0 main@entry_0)
             (= main@%.tr2.i_1 main@%.tr2.i_0))
         main@.lr.ph.i_0)
    (main@.lr.ph.i @nd_0
                   main@%sh3_0
                   main@%_2_0
                   main@%_0_0
                   main@%_4_0
                   main@%_3_0
                   main@%.tr2.i_1)))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_0_0 0)
                (= main@%.0.sroa_cast_0 main@%_0_0)
                (nd_tree true false false main@%sh_0 main@%_1_0)
                (= main@%sm_0 (store main@%sh_0 main@%_0_0 main@%_1_0))
                (nd_tree true false false main@%sh1_0 main@%_2_0)
                (sum true
                     false
                     false
                     main@%sh1_0
                     main@%sh2_0
                     main@%_1_0
                     main@%_3_0)
                (sum true
                     false
                     false
                     main@%sh2_0
                     main@%sh3_0
                     main@%_2_0
                     main@%_4_0)
                (= main@%_5_0 (= main@%_1_0 0))
                (=> main@append.exit_0 (and main@append.exit_0 main@entry_0))
                (=> (and main@append.exit_0 main@entry_0) main@%_5_0)
                (=> (and main@append.exit_0 main@entry_0)
                    (= main@%.tr.lcssa.i_0 main@%_0_0))
                (=> (and main@append.exit_0 main@entry_0)
                    (= main@%.tr.lcssa.i_1 main@%.tr.lcssa.i_0))
                (=> main@append.exit_0
                    (= main@%sm4_0
                       (store main@%sh3_0 main@%.tr.lcssa.i_1 main@%_2_0)))
                (=> main@append.exit_0
                    (= main@%.0.1_0 (select main@%sm4_0 main@%_0_0)))
                (sum main@append.exit_0
                     false
                     false
                     main@%sm4_0
                     main@%sh5_0
                     main@%.0.1_0
                     main@%_14_0)
                (=> main@append.exit_0
                    (= main@%_15_0 (+ main@%_4_0 main@%_3_0)))
                (=> main@append.exit_0
                    (= main@%_16_0 (= main@%_14_0 main@%_15_0)))
                (=> main@append.exit_0 (not main@%_16_0))
                (=> main@append.exit.split_0
                    (and main@append.exit.split_0 main@append.exit_0))
                main@append.exit.split_0)))
  (=> a!1 main@append.exit.split)))
(rule (let ((a!1 (= main@%_10_0 (+ (+ main@%_9_0 (* 0 12)) 4)))
      (a!2 (= main@%_11_0 (+ (+ main@%_9_0 (* 0 12)) 8))))
  (=> (and (main@.lr.ph.i @nd_0
                          main@%sh3_0
                          main@%_2_0
                          main@%_0_0
                          main@%_4_0
                          main@%_3_0
                          main@%.tr2.i_0)
           true
           (= main@%_6_0 @nd_0)
           (= main@%_8_0 (= main@%_7_0 0))
           (= main@%_9_0 (select main@%sh3_0 main@%.tr2.i_0))
           a!1
           (or (<= main@%_9_0 0) (> main@%_10_0 0))
           a!2
           (or (<= main@%_9_0 0) (> main@%_11_0 0))
           (= main@%.tr.be.i_0 (ite main@%_8_0 main@%_11_0 main@%_10_0))
           (= main@%_12_0 (select main@%sh3_0 main@%.tr.be.i_0))
           (= main@%_13_0 (= main@%_12_0 0))
           (=> main@.lr.ph.i_1 (and main@.lr.ph.i_1 main@.lr.ph.i_0))
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0) (not main@%_13_0))
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0)
               (= main@%.tr2.i_1 main@%.tr.be.i_0))
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0)
               (= main@%.tr2.i_2 main@%.tr2.i_1))
           main@.lr.ph.i_1)
      (main@.lr.ph.i @nd_0
                     main@%sh3_0
                     main@%_2_0
                     main@%_0_0
                     main@%_4_0
                     main@%_3_0
                     main@%.tr2.i_2))))
(rule (let ((a!1 (= main@%_10_0 (+ (+ main@%_9_0 (* 0 12)) 4)))
      (a!2 (= main@%_11_0 (+ (+ main@%_9_0 (* 0 12)) 8))))
(let ((a!3 (and (main@.lr.ph.i @nd_0
                               main@%sh3_0
                               main@%_2_0
                               main@%_0_0
                               main@%_4_0
                               main@%_3_0
                               main@%.tr2.i_0)
                true
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (= main@%_7_0 0))
                (= main@%_9_0 (select main@%sh3_0 main@%.tr2.i_0))
                a!1
                (or (<= main@%_9_0 0) (> main@%_10_0 0))
                a!2
                (or (<= main@%_9_0 0) (> main@%_11_0 0))
                (= main@%.tr.be.i_0 (ite main@%_8_0 main@%_11_0 main@%_10_0))
                (= main@%_12_0 (select main@%sh3_0 main@%.tr.be.i_0))
                (= main@%_13_0 (= main@%_12_0 0))
                (=> main@append.exit_0 (and main@append.exit_0 main@.lr.ph.i_0))
                (=> (and main@append.exit_0 main@.lr.ph.i_0) main@%_13_0)
                (=> (and main@append.exit_0 main@.lr.ph.i_0)
                    (= main@%.tr.lcssa.i_0 main@%.tr.be.i_0))
                (=> (and main@append.exit_0 main@.lr.ph.i_0)
                    (= main@%.tr.lcssa.i_1 main@%.tr.lcssa.i_0))
                (=> main@append.exit_0
                    (= main@%sm4_0
                       (store main@%sh3_0 main@%.tr.lcssa.i_1 main@%_2_0)))
                (=> main@append.exit_0
                    (= main@%.0.1_0 (select main@%sm4_0 main@%_0_0)))
                (sum main@append.exit_0
                     false
                     false
                     main@%sm4_0
                     main@%sh5_0
                     main@%.0.1_0
                     main@%_14_0)
                (=> main@append.exit_0
                    (= main@%_15_0 (+ main@%_4_0 main@%_3_0)))
                (=> main@append.exit_0
                    (= main@%_16_0 (= main@%_14_0 main@%_15_0)))
                (=> main@append.exit_0 (not main@%_16_0))
                (=> main@append.exit.split_0
                    (and main@append.exit.split_0 main@append.exit_0))
                main@append.exit.split_0)))
  (=> a!3 main@append.exit.split))))
(query main@append.exit.split)

