(set-info :original "7-trees/0-append-some-sum-1.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_tree@_1 ((Array Int Int) Int ))
(declare-rel nd_tree@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_tree (Bool Bool Bool (Array Int Int) Int ))
(declare-rel sum@_1 ((Array Int Int) Int ))
(declare-rel sum@tailrecurse ((Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel sum@tailrecurse._crit_edge.split ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel sum (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph.i (Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@append_some.exit.split ())
(declare-var nd_tree@%_7_0 Int )
(declare-var nd_tree@%_9_0 (Array Int Int) )
(declare-var nd_tree@%_10_0 Int )
(declare-var nd_tree@%_11_0 Int )
(declare-var nd_tree@%_12_0 Int )
(declare-var nd_tree@%_store_0 (Array Int Int) )
(declare-var nd_tree@%_14_0 (Array Int Int) )
(declare-var nd_tree@%_15_0 Int )
(declare-var nd_tree@%_16_0 Int )
(declare-var nd_tree@%_17_0 Int )
(declare-var nd_tree@%_tail_0 (Array Int Int) )
(declare-var nd_tree@%shadow.mem.0_2 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_2 Int )
(declare-var nd_tree@%_3_0 Int )
(declare-var @nd_0 Int )
(declare-var nd_tree@%_4_0 Int )
(declare-var nd_tree@%_br_0 Bool )
(declare-var nd_tree@%shadow.mem.0_0 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_0 Int )
(declare-var nd_tree@_1_0 Bool )
(declare-var nd_tree@_br2_0 Bool )
(declare-var nd_tree@_6_0 Bool )
(declare-var nd_tree@%_8_0 Int )
(declare-var nd_tree@%_store1_0 (Array Int Int) )
(declare-var nd_tree@UnifiedReturnBlock_0 Bool )
(declare-var nd_tree@%shadow.mem.0_1 (Array Int Int) )
(declare-var nd_tree@%UnifiedRetVal_1 Int )
(declare-var nd_tree@UnifiedReturnBlock.split_0 Bool )
(declare-var sum@%_call_0 Int )
(declare-var sum@%_5_0 Int )
(declare-var sum@%_7_0 Int )
(declare-var sum@%_call1_0 Int )
(declare-var sum@%_9_0 Int )
(declare-var sum@%_call2_0 Int )
(declare-var sum@%_12_0 Int )
(declare-var sum@%_br4_0 Bool )
(declare-var sum@%.lcssa_1 Int )
(declare-var sum@%shadow.mem.0_2 (Array Int Int) )
(declare-var sum@%xs.tr2_2 Int )
(declare-var sum@%accumulator.tr1_2 Int )
(declare-var sum@%_br_0 Bool )
(declare-var sum@%_tail_0 (Array Int Int) )
(declare-var sum@%shadow.mem.1_0 (Array Int Int) )
(declare-var sum@%xs_0 Int )
(declare-var sum@%accumulator.tr.lcssa_0 Int )
(declare-var sum@_1_0 Bool )
(declare-var sum@tailrecurse.preheader_0 Bool )
(declare-var sum@tailrecurse_0 Bool )
(declare-var sum@%shadow.mem.0_0 (Array Int Int) )
(declare-var sum@%xs.tr2_0 Int )
(declare-var sum@%accumulator.tr1_0 Int )
(declare-var sum@%shadow.mem.0_1 (Array Int Int) )
(declare-var sum@%xs.tr2_1 Int )
(declare-var sum@%accumulator.tr1_1 Int )
(declare-var sum@tailrecurse._crit_edge_0 Bool )
(declare-var sum@%shadow.mem.1_1 (Array Int Int) )
(declare-var sum@%accumulator.tr.lcssa_1 Int )
(declare-var sum@tailrecurse._crit_edge.split_0 Bool )
(declare-var sum@%_6_0 (Array Int Int) )
(declare-var sum@%_11_0 Int )
(declare-var sum@%_tail3_0 Int )
(declare-var sum@tailrecurse_1 Bool )
(declare-var sum@tailrecurse._crit_edge.loopexit_0 Bool )
(declare-var sum@%.lcssa_0 Int )
(declare-var main@%_19_0 (Array Int Int) )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 (Array Int Int) )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%pxs.tr.be.i.lcssa_1 Int )
(declare-var main@%pxs.tr1.i_2 Int )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 (Array Int Int) )
(declare-var main@%_4_0 (Array Int Int) )
(declare-var main@%_6_0 (Array Int Int) )
(declare-var main@%_10_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%xs.i_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@.lr.ph.i.preheader_0 Bool )
(declare-var main@.lr.ph.i_0 Bool )
(declare-var main@%pxs.tr1.i_0 Int )
(declare-var main@%pxs.tr1.i_1 Int )
(declare-var main@append_some.exit_0 Bool )
(declare-var main@%pxs.tr.lcssa.i_0 Int )
(declare-var main@%pxs.tr.lcssa.i_1 Int )
(declare-var main@append_some.exit.split_0 Bool )
(declare-var main@%pxs.tr.be.i_0 Int )
(declare-var main@.lr.ph.i_1 Bool )
(declare-var main@append_some.exit.loopexit_0 Bool )
(declare-var main@%pxs.tr.be.i.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (nd_tree true true true nd_tree@%shadow.mem.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree false true true nd_tree@%shadow.mem.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree false false false nd_tree@%shadow.mem.0_0 nd_tree@%UnifiedRetVal_0))
(rule (nd_tree@_1 nd_tree@%_tail_0 @nd_0))
(rule (let ((a!1 (=> nd_tree@_6_0 (= nd_tree@%_11_0 (+ nd_tree@%_7_0 (* 4 1)))))
      (a!2 (=> nd_tree@_6_0 (= nd_tree@%_16_0 (+ nd_tree@%_7_0 (* 8 1))))))
(let ((a!3 (and (nd_tree@_1 nd_tree@%_tail_0 @nd_0)
                true
                (= nd_tree@%_3_0 @nd_0)
                (= nd_tree@%_br_0 (= nd_tree@%_4_0 0))
                (=> nd_tree@_br2_0 (and nd_tree@_br2_0 nd_tree@_1_0))
                (=> (and nd_tree@_br2_0 nd_tree@_1_0) (not nd_tree@%_br_0))
                (=> nd_tree@_6_0 (and nd_tree@_6_0 nd_tree@_1_0))
                (=> (and nd_tree@_6_0 nd_tree@_1_0) nd_tree@%_br_0)
                (=> nd_tree@_6_0 (= nd_tree@%_8_0 nd_tree@%_7_0))
                (nd_tree nd_tree@_6_0 false false nd_tree@%_9_0 nd_tree@%_10_0)
                a!1
                (=> nd_tree@_6_0 (or (<= nd_tree@%_7_0 0) (> nd_tree@%_11_0 0)))
                (=> nd_tree@_6_0 (= nd_tree@%_12_0 nd_tree@%_11_0))
                (=> nd_tree@_6_0 (> nd_tree@%_7_0 0))
                (=> nd_tree@_6_0
                    (= nd_tree@%_store_0
                       (store nd_tree@%_9_0 nd_tree@%_12_0 nd_tree@%_10_0)))
                (nd_tree nd_tree@_6_0 false false nd_tree@%_14_0 nd_tree@%_15_0)
                a!2
                (=> nd_tree@_6_0 (or (<= nd_tree@%_7_0 0) (> nd_tree@%_16_0 0)))
                (=> nd_tree@_6_0 (= nd_tree@%_17_0 nd_tree@%_16_0))
                (=> nd_tree@_6_0 (> nd_tree@%_7_0 0))
                (=> nd_tree@_6_0
                    (= nd_tree@%_store1_0
                       (store nd_tree@%_14_0 nd_tree@%_17_0 nd_tree@%_15_0)))
                (=> nd_tree@UnifiedReturnBlock_0
                    (or (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br2_0)
                        (and nd_tree@UnifiedReturnBlock_0 nd_tree@_6_0)))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br2_0)
                    (= nd_tree@%shadow.mem.0_0 nd_tree@%_tail_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br2_0)
                    (= nd_tree@%UnifiedRetVal_0 0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_6_0)
                    (= nd_tree@%shadow.mem.0_1 nd_tree@%_store1_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_6_0)
                    (= nd_tree@%UnifiedRetVal_1 nd_tree@%_8_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br2_0)
                    (= nd_tree@%shadow.mem.0_2 nd_tree@%shadow.mem.0_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_br2_0)
                    (= nd_tree@%UnifiedRetVal_2 nd_tree@%UnifiedRetVal_0))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_6_0)
                    (= nd_tree@%shadow.mem.0_2 nd_tree@%shadow.mem.0_1))
                (=> (and nd_tree@UnifiedReturnBlock_0 nd_tree@_6_0)
                    (= nd_tree@%UnifiedRetVal_2 nd_tree@%UnifiedRetVal_1))
                (=> nd_tree@UnifiedReturnBlock.split_0
                    (and nd_tree@UnifiedReturnBlock.split_0
                         nd_tree@UnifiedReturnBlock_0))
                nd_tree@UnifiedReturnBlock.split_0)))
  (=> a!3
      (nd_tree@UnifiedReturnBlock.split
        nd_tree@%shadow.mem.0_2
        nd_tree@%UnifiedRetVal_2
        nd_tree@%_tail_0
        @nd_0)))))
(rule (=> (nd_tree@UnifiedReturnBlock.split
      nd_tree@%shadow.mem.0_0
      nd_tree@%UnifiedRetVal_0
      nd_tree@%_tail_0
      @nd_0)
    (nd_tree true false false nd_tree@%shadow.mem.0_0 nd_tree@%UnifiedRetVal_0)))
(rule (sum true
     true
     true
     sum@%_tail_0
     sum@%shadow.mem.1_0
     sum@%xs_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum false
     true
     true
     sum@%_tail_0
     sum@%shadow.mem.1_0
     sum@%xs_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum false
     false
     false
     sum@%_tail_0
     sum@%shadow.mem.1_0
     sum@%xs_0
     sum@%accumulator.tr.lcssa_0))
(rule (sum@_1 sum@%_tail_0 sum@%xs_0))
(rule (=> (and (sum@_1 sum@%_tail_0 sum@%xs_0)
         true
         (= sum@%_br_0 (= sum@%xs_0 0))
         (=> sum@tailrecurse.preheader_0
             (and sum@tailrecurse.preheader_0 sum@_1_0))
         (=> (and sum@tailrecurse.preheader_0 sum@_1_0) (not sum@%_br_0))
         (=> sum@tailrecurse_0
             (and sum@tailrecurse_0 sum@tailrecurse.preheader_0))
         sum@tailrecurse_0
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%shadow.mem.0_0 sum@%_tail_0))
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%xs.tr2_0 sum@%xs_0))
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%accumulator.tr1_0 0))
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%shadow.mem.0_1 sum@%shadow.mem.0_0))
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%xs.tr2_1 sum@%xs.tr2_0))
         (=> (and sum@tailrecurse_0 sum@tailrecurse.preheader_0)
             (= sum@%accumulator.tr1_1 sum@%accumulator.tr1_0)))
    (sum@tailrecurse sum@%_tail_0
                     sum@%xs.tr2_1
                     sum@%shadow.mem.0_1
                     sum@%accumulator.tr1_1
                     sum@%xs_0)))
(rule (=> (and (sum@_1 sum@%_tail_0 sum@%xs_0)
         true
         (= sum@%_br_0 (= sum@%xs_0 0))
         (=> sum@tailrecurse._crit_edge_0
             (and sum@tailrecurse._crit_edge_0 sum@_1_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_1_0) sum@%_br_0)
         (=> (and sum@tailrecurse._crit_edge_0 sum@_1_0)
             (= sum@%shadow.mem.1_0 sum@%_tail_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_1_0)
             (= sum@%accumulator.tr.lcssa_0 0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_1_0)
             (= sum@%shadow.mem.1_1 sum@%shadow.mem.1_0))
         (=> (and sum@tailrecurse._crit_edge_0 sum@_1_0)
             (= sum@%accumulator.tr.lcssa_1 sum@%accumulator.tr.lcssa_0))
         (=> sum@tailrecurse._crit_edge.split_0
             (and sum@tailrecurse._crit_edge.split_0
                  sum@tailrecurse._crit_edge_0))
         sum@tailrecurse._crit_edge.split_0)
    (sum@tailrecurse._crit_edge.split
      sum@%_tail_0
      sum@%shadow.mem.1_1
      sum@%accumulator.tr.lcssa_1
      sum@%xs_0)))
(rule (let ((a!1 (= sum@%_call_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 4)))
      (a!2 (= sum@%_call1_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 0)))
      (a!3 (= sum@%_call2_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 8))))
  (=> (and (sum@tailrecurse sum@%_tail_0
                            sum@%xs.tr2_0
                            sum@%shadow.mem.0_0
                            sum@%accumulator.tr1_0
                            sum@%xs_0)
           true
           a!1
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call_0 0))
           (> sum@%xs.tr2_0 0)
           (= sum@%_5_0 (select sum@%shadow.mem.0_0 sum@%_call_0))
           (sum true
                false
                false
                sum@%shadow.mem.0_0
                sum@%_6_0
                sum@%_5_0
                sum@%_7_0)
           a!2
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call1_0 0))
           (= sum@%_9_0 (select sum@%_6_0 sum@%_call1_0))
           a!3
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call2_0 0))
           (> sum@%xs.tr2_0 0)
           (= sum@%_11_0 (select sum@%_6_0 sum@%_call2_0))
           (= sum@%_12_0 (+ sum@%_7_0 sum@%accumulator.tr1_0))
           (= sum@%_tail3_0 (+ sum@%_12_0 sum@%_9_0))
           (= sum@%_br4_0 (= sum@%_11_0 0))
           (=> sum@tailrecurse_1 (and sum@tailrecurse_1 sum@tailrecurse_0))
           sum@tailrecurse_1
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0) (not sum@%_br4_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%shadow.mem.0_1 sum@%_6_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%xs.tr2_1 sum@%_11_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%accumulator.tr1_1 sum@%_tail3_0))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%shadow.mem.0_2 sum@%shadow.mem.0_1))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%xs.tr2_2 sum@%xs.tr2_1))
           (=> (and sum@tailrecurse_1 sum@tailrecurse_0)
               (= sum@%accumulator.tr1_2 sum@%accumulator.tr1_1)))
      (sum@tailrecurse sum@%_tail_0
                       sum@%xs.tr2_2
                       sum@%shadow.mem.0_2
                       sum@%accumulator.tr1_2
                       sum@%xs_0))))
(rule (let ((a!1 (= sum@%_call_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 4)))
      (a!2 (= sum@%_call1_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 0)))
      (a!3 (= sum@%_call2_0 (+ (+ sum@%xs.tr2_0 (* 0 12)) 8))))
  (=> (and (sum@tailrecurse sum@%_tail_0
                            sum@%xs.tr2_0
                            sum@%shadow.mem.0_0
                            sum@%accumulator.tr1_0
                            sum@%xs_0)
           true
           a!1
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call_0 0))
           (> sum@%xs.tr2_0 0)
           (= sum@%_5_0 (select sum@%shadow.mem.0_0 sum@%_call_0))
           (sum true
                false
                false
                sum@%shadow.mem.0_0
                sum@%_6_0
                sum@%_5_0
                sum@%_7_0)
           a!2
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call1_0 0))
           (= sum@%_9_0 (select sum@%_6_0 sum@%_call1_0))
           a!3
           (or (<= sum@%xs.tr2_0 0) (> sum@%_call2_0 0))
           (> sum@%xs.tr2_0 0)
           (= sum@%_11_0 (select sum@%_6_0 sum@%_call2_0))
           (= sum@%_12_0 (+ sum@%_7_0 sum@%accumulator.tr1_0))
           (= sum@%_tail3_0 (+ sum@%_12_0 sum@%_9_0))
           (= sum@%_br4_0 (= sum@%_11_0 0))
           (=> sum@tailrecurse._crit_edge.loopexit_0
               (and sum@tailrecurse._crit_edge.loopexit_0 sum@tailrecurse_0))
           (=> (and sum@tailrecurse._crit_edge.loopexit_0 sum@tailrecurse_0)
               sum@%_br4_0)
           (=> (and sum@tailrecurse._crit_edge.loopexit_0 sum@tailrecurse_0)
               (= sum@%.lcssa_0 sum@%_tail3_0))
           (=> (and sum@tailrecurse._crit_edge.loopexit_0 sum@tailrecurse_0)
               (= sum@%.lcssa_1 sum@%.lcssa_0))
           (=> sum@tailrecurse._crit_edge_0
               (and sum@tailrecurse._crit_edge_0
                    sum@tailrecurse._crit_edge.loopexit_0))
           (=> (and sum@tailrecurse._crit_edge_0
                    sum@tailrecurse._crit_edge.loopexit_0)
               (= sum@%shadow.mem.1_0 sum@%_6_0))
           (=> (and sum@tailrecurse._crit_edge_0
                    sum@tailrecurse._crit_edge.loopexit_0)
               (= sum@%accumulator.tr.lcssa_0 sum@%.lcssa_1))
           (=> (and sum@tailrecurse._crit_edge_0
                    sum@tailrecurse._crit_edge.loopexit_0)
               (= sum@%shadow.mem.1_1 sum@%shadow.mem.1_0))
           (=> (and sum@tailrecurse._crit_edge_0
                    sum@tailrecurse._crit_edge.loopexit_0)
               (= sum@%accumulator.tr.lcssa_1 sum@%accumulator.tr.lcssa_0))
           (=> sum@tailrecurse._crit_edge.split_0
               (and sum@tailrecurse._crit_edge.split_0
                    sum@tailrecurse._crit_edge_0))
           sum@tailrecurse._crit_edge.split_0)
      (sum@tailrecurse._crit_edge.split
        sum@%_tail_0
        sum@%shadow.mem.1_1
        sum@%accumulator.tr.lcssa_1
        sum@%xs_0))))
(rule (=> (sum@tailrecurse._crit_edge.split
      sum@%_tail_0
      sum@%shadow.mem.1_0
      sum@%accumulator.tr.lcssa_0
      sum@%xs_0)
    (sum true
         false
         false
         sum@%_tail_0
         sum@%shadow.mem.1_0
         sum@%xs_0
         sum@%accumulator.tr.lcssa_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (> main@%xs.i_0 0)
         (nd_tree true false false main@%_1_0 main@%_2_0)
         (= main@%_3_0 (store main@%_1_0 main@%xs.i_0 main@%_2_0))
         (nd_tree true false false main@%_4_0 main@%_5_0)
         (sum true false false main@%_4_0 main@%_6_0 main@%_2_0 main@%_7_0)
         (sum true false false main@%_6_0 main@%_8_0 main@%_5_0 main@%_9_0)
         (= main@%_10_0 (= main@%_2_0 0))
         (=> main@.lr.ph.i.preheader_0
             (and main@.lr.ph.i.preheader_0 main@entry_0))
         (=> (and main@.lr.ph.i.preheader_0 main@entry_0) (not main@%_10_0))
         (=> main@.lr.ph.i_0 (and main@.lr.ph.i_0 main@.lr.ph.i.preheader_0))
         main@.lr.ph.i_0
         (=> (and main@.lr.ph.i_0 main@.lr.ph.i.preheader_0)
             (= main@%pxs.tr1.i_0 main@%xs.i_0))
         (=> (and main@.lr.ph.i_0 main@.lr.ph.i.preheader_0)
             (= main@%pxs.tr1.i_1 main@%pxs.tr1.i_0)))
    (main@.lr.ph.i @nd_0
                   main@%_8_0
                   main@%_5_0
                   main@%xs.i_0
                   main@%_9_0
                   main@%_7_0
                   main@%pxs.tr1.i_1)))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%xs.i_0 0)
                (nd_tree true false false main@%_1_0 main@%_2_0)
                (= main@%_3_0 (store main@%_1_0 main@%xs.i_0 main@%_2_0))
                (nd_tree true false false main@%_4_0 main@%_5_0)
                (sum true
                     false
                     false
                     main@%_4_0
                     main@%_6_0
                     main@%_2_0
                     main@%_7_0)
                (sum true
                     false
                     false
                     main@%_6_0
                     main@%_8_0
                     main@%_5_0
                     main@%_9_0)
                (= main@%_10_0 (= main@%_2_0 0))
                (=> main@append_some.exit_0
                    (and main@append_some.exit_0 main@entry_0))
                (=> (and main@append_some.exit_0 main@entry_0) main@%_10_0)
                (=> (and main@append_some.exit_0 main@entry_0)
                    (= main@%pxs.tr.lcssa.i_0 main@%xs.i_0))
                (=> (and main@append_some.exit_0 main@entry_0)
                    (= main@%pxs.tr.lcssa.i_1 main@%pxs.tr.lcssa.i_0))
                (=> main@append_some.exit_0
                    (= main@%_19_0
                       (store main@%_8_0 main@%pxs.tr.lcssa.i_1 main@%_5_0)))
                (=> main@append_some.exit_0
                    (= main@%_20_0 (select main@%_19_0 main@%xs.i_0)))
                (sum main@append_some.exit_0
                     false
                     false
                     main@%_19_0
                     main@%_21_0
                     main@%_20_0
                     main@%_22_0)
                (=> main@append_some.exit_0
                    (= main@%_23_0 (+ main@%_9_0 main@%_7_0)))
                (=> main@append_some.exit_0
                    (= main@%_24_0 (> main@%_22_0 main@%_23_0)))
                (=> main@append_some.exit_0 (not main@%_24_0))
                (=> main@append_some.exit.split_0
                    (and main@append_some.exit.split_0 main@append_some.exit_0))
                main@append_some.exit.split_0)))
  (=> a!1 main@append_some.exit.split)))
(rule (let ((a!1 (= main@%_15_0 (+ (+ main@%_14_0 (* 0 12)) 4)))
      (a!2 (= main@%_16_0 (+ (+ main@%_14_0 (* 0 12)) 8))))
  (=> (and (main@.lr.ph.i @nd_0
                          main@%_8_0
                          main@%_5_0
                          main@%xs.i_0
                          main@%_9_0
                          main@%_7_0
                          main@%pxs.tr1.i_0)
           true
           (= main@%_11_0 @nd_0)
           (= main@%_13_0 (= main@%_12_0 0))
           (= main@%_14_0 (select main@%_8_0 main@%pxs.tr1.i_0))
           a!1
           (or (<= main@%_14_0 0) (> main@%_15_0 0))
           a!2
           (or (<= main@%_14_0 0) (> main@%_16_0 0))
           (= main@%pxs.tr.be.i_0 (ite main@%_13_0 main@%_16_0 main@%_15_0))
           (= main@%_17_0 (select main@%_8_0 main@%pxs.tr.be.i_0))
           (= main@%_18_0 (= main@%_17_0 0))
           (=> main@.lr.ph.i_1 (and main@.lr.ph.i_1 main@.lr.ph.i_0))
           main@.lr.ph.i_1
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0) (not main@%_18_0))
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0)
               (= main@%pxs.tr1.i_1 main@%pxs.tr.be.i_0))
           (=> (and main@.lr.ph.i_1 main@.lr.ph.i_0)
               (= main@%pxs.tr1.i_2 main@%pxs.tr1.i_1)))
      (main@.lr.ph.i @nd_0
                     main@%_8_0
                     main@%_5_0
                     main@%xs.i_0
                     main@%_9_0
                     main@%_7_0
                     main@%pxs.tr1.i_2))))
(rule (let ((a!1 (= main@%_15_0 (+ (+ main@%_14_0 (* 0 12)) 4)))
      (a!2 (= main@%_16_0 (+ (+ main@%_14_0 (* 0 12)) 8))))
(let ((a!3 (and (main@.lr.ph.i @nd_0
                               main@%_8_0
                               main@%_5_0
                               main@%xs.i_0
                               main@%_9_0
                               main@%_7_0
                               main@%pxs.tr1.i_0)
                true
                (= main@%_11_0 @nd_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (= main@%_14_0 (select main@%_8_0 main@%pxs.tr1.i_0))
                a!1
                (or (<= main@%_14_0 0) (> main@%_15_0 0))
                a!2
                (or (<= main@%_14_0 0) (> main@%_16_0 0))
                (= main@%pxs.tr.be.i_0
                   (ite main@%_13_0 main@%_16_0 main@%_15_0))
                (= main@%_17_0 (select main@%_8_0 main@%pxs.tr.be.i_0))
                (= main@%_18_0 (= main@%_17_0 0))
                (=> main@append_some.exit.loopexit_0
                    (and main@append_some.exit.loopexit_0 main@.lr.ph.i_0))
                (=> (and main@append_some.exit.loopexit_0 main@.lr.ph.i_0)
                    main@%_18_0)
                (=> (and main@append_some.exit.loopexit_0 main@.lr.ph.i_0)
                    (= main@%pxs.tr.be.i.lcssa_0 main@%pxs.tr.be.i_0))
                (=> (and main@append_some.exit.loopexit_0 main@.lr.ph.i_0)
                    (= main@%pxs.tr.be.i.lcssa_1 main@%pxs.tr.be.i.lcssa_0))
                (=> main@append_some.exit_0
                    (and main@append_some.exit_0
                         main@append_some.exit.loopexit_0))
                (=> (and main@append_some.exit_0
                         main@append_some.exit.loopexit_0)
                    (= main@%pxs.tr.lcssa.i_0 main@%pxs.tr.be.i.lcssa_1))
                (=> (and main@append_some.exit_0
                         main@append_some.exit.loopexit_0)
                    (= main@%pxs.tr.lcssa.i_1 main@%pxs.tr.lcssa.i_0))
                (=> main@append_some.exit_0
                    (= main@%_19_0
                       (store main@%_8_0 main@%pxs.tr.lcssa.i_1 main@%_5_0)))
                (=> main@append_some.exit_0
                    (= main@%_20_0 (select main@%_19_0 main@%xs.i_0)))
                (sum main@append_some.exit_0
                     false
                     false
                     main@%_19_0
                     main@%_21_0
                     main@%_20_0
                     main@%_22_0)
                (=> main@append_some.exit_0
                    (= main@%_23_0 (+ main@%_9_0 main@%_7_0)))
                (=> main@append_some.exit_0
                    (= main@%_24_0 (> main@%_22_0 main@%_23_0)))
                (=> main@append_some.exit_0 (not main@%_24_0))
                (=> main@append_some.exit.split_0
                    (and main@append_some.exit.split_0 main@append_some.exit_0))
                main@append_some.exit.split_0)))
  (=> a!3 main@append_some.exit.split))))
(query main@append_some.exit.split)

