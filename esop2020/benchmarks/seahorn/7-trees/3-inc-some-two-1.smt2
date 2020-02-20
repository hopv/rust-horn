(set-info :original "7-trees/3-inc-some-two-1.bc")
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
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i4 (Int Int (Array Int Int) Int Int ))
(declare-rel main@some.exit10.split ())
(declare-rel main@tailrecurse.us.i3 ())
(declare-rel main@tailrecurse.us.i ())
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
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%xs.tr.ph.be.in.i_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%xs.tr.ph.be.in.i7_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 (Array Int Int) )
(declare-var main@%_41_0 (Array Int Int) )
(declare-var main@%_42_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%xs.tr.ph.i113.lcssa_1 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%xs.tr.ph.i14.lcssa_1 Int )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_5_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 (Array Int Int) )
(declare-var main@%_4_0 Int )
(declare-var main@tailrecurse.i.preheader_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%xs.tr.ph.i14_0 Int )
(declare-var main@%xs.tr.ph.i14_1 Int )
(declare-var main@tailrecurse.us.i.preheader_0 Bool )
(declare-var main@tailrecurse.us.i_0 Bool )
(declare-var main@tailrecurse.outer.backedge.i_0 Bool )
(declare-var main@%xs.tr.ph.be.i_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%xs.tr.ph.i14_2 Int )
(declare-var main@tailrecurse.i4.preheader_0 Bool )
(declare-var main@%xs.tr.ph.i14.lcssa_0 Int )
(declare-var main@%_20_0 (Array Int Int) )
(declare-var main@%_25_0 Int )
(declare-var main@tailrecurse.i4_0 Bool )
(declare-var main@%xs.tr.ph.i113_0 Int )
(declare-var main@%xs.tr.ph.i113_1 Int )
(declare-var main@tailrecurse.us.i.preheader.loopexit_0 Bool )
(declare-var main@tailrecurse.outer.backedge.i9_0 Bool )
(declare-var main@%xs.tr.ph.be.i8_0 Int )
(declare-var main@tailrecurse.i4_1 Bool )
(declare-var main@%xs.tr.ph.i113_2 Int )
(declare-var main@some.exit10_0 Bool )
(declare-var main@%xs.tr.ph.i113.lcssa_0 Int )
(declare-var main@some.exit10.split_0 Bool )
(declare-var main@tailrecurse.us.i3.preheader_0 Bool )
(declare-var main@tailrecurse.us.i3_0 Bool )
(declare-var main@tailrecurse.us.i3_1 Bool )
(declare-var main@tailrecurse.us.i_1 Bool )
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
         (nd_tree true false false main@%_1_0 main@%_2_0)
         (sum true false false main@%_1_0 main@%_3_0 main@%_2_0 main@%_4_0)
         (= main@%_5_0 (= main@%_2_0 0))
         (=> main@tailrecurse.i.preheader_0
             (and main@tailrecurse.i.preheader_0 main@entry_0))
         (=> (and main@tailrecurse.i.preheader_0 main@entry_0) (not main@%_5_0))
         (=> main@tailrecurse.i_0
             (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%xs.tr.ph.i14_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%xs.tr.ph.i14_1 main@%xs.tr.ph.i14_0)))
    (main@tailrecurse.i
      @nd_0
      main@%xs.tr.ph.i14_1
      main@%_3_0
      main@%_2_0
      main@%_4_0)))
(rule (=> (and (main@entry @nd_0)
         true
         (nd_tree true false false main@%_1_0 main@%_2_0)
         (sum true false false main@%_1_0 main@%_3_0 main@%_2_0 main@%_4_0)
         (= main@%_5_0 (= main@%_2_0 0))
         (=> main@tailrecurse.us.i.preheader_0
             (and main@tailrecurse.us.i.preheader_0 main@entry_0))
         (=> (and main@tailrecurse.us.i.preheader_0 main@entry_0) main@%_5_0)
         (=> main@tailrecurse.us.i_0
             (and main@tailrecurse.us.i_0 main@tailrecurse.us.i.preheader_0))
         main@tailrecurse.us.i_0)
    main@tailrecurse.us.i))
(rule (let ((a!1 (= main@%_12_0 (+ (+ main@%xs.tr.ph.i14_0 (* 0 12)) 8)))
      (a!2 (= main@%_13_0 (+ (+ main@%xs.tr.ph.i14_0 (* 0 12)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%xs.tr.ph.i14_0
                  main@%_3_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (= main@%_7_0 0))
                (=> main@tailrecurse.outer.backedge.i_0
                    (and main@tailrecurse.outer.backedge.i_0
                         main@tailrecurse.i_0))
                (=> (and main@tailrecurse.outer.backedge.i_0
                         main@tailrecurse.i_0)
                    main@%_8_0)
                (=> main@tailrecurse.outer.backedge.i_0 (= main@%_9_0 @nd_0))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%_11_0 (= main@%_10_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0 a!1)
                (=> main@tailrecurse.outer.backedge.i_0
                    (or (<= main@%xs.tr.ph.i14_0 0) (> main@%_12_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0 a!2)
                (=> main@tailrecurse.outer.backedge.i_0
                    (or (<= main@%xs.tr.ph.i14_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%xs.tr.ph.be.in.i_0
                       (ite main@%_11_0 main@%_12_0 main@%_13_0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%xs.tr.ph.be.i_0
                       (select main@%_3_0 main@%xs.tr.ph.be.in.i_0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%_14_0 (= main@%xs.tr.ph.be.i_0 0)))
                (=> main@tailrecurse.i_1
                    (and main@tailrecurse.i_1
                         main@tailrecurse.outer.backedge.i_0))
                main@tailrecurse.i_1
                (=> (and main@tailrecurse.i_1
                         main@tailrecurse.outer.backedge.i_0)
                    (not main@%_14_0))
                (=> (and main@tailrecurse.i_1
                         main@tailrecurse.outer.backedge.i_0)
                    (= main@%xs.tr.ph.i14_1 main@%xs.tr.ph.be.i_0))
                (=> (and main@tailrecurse.i_1
                         main@tailrecurse.outer.backedge.i_0)
                    (= main@%xs.tr.ph.i14_2 main@%xs.tr.ph.i14_1)))))
  (=> a!3
      (main@tailrecurse.i
        @nd_0
        main@%xs.tr.ph.i14_2
        main@%_3_0
        main@%_2_0
        main@%_4_0)))))
(rule (let ((a!1 (= main@%_15_0 (+ (+ main@%xs.tr.ph.i14.lcssa_1 (* 0 12)) 0)))
      (a!2 (=> main@tailrecurse.i4.preheader_0
               (= main@%_21_0 (not (= main@%_17_0 0)))))
      (a!3 (= main@%_22_0 (+ (+ main@%xs.tr.ph.i14.lcssa_1 (* 0 12)) 4)))
      (a!4 (= main@%_23_0 (+ (+ main@%xs.tr.ph.i14.lcssa_1 (* 0 12)) 8))))
(let ((a!5 (and (main@tailrecurse.i
                  @nd_0
                  main@%xs.tr.ph.i14_0
                  main@%_3_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (= main@%_7_0 0))
                (=> main@tailrecurse.i4.preheader_0
                    (and main@tailrecurse.i4.preheader_0 main@tailrecurse.i_0))
                (=> (and main@tailrecurse.i4.preheader_0 main@tailrecurse.i_0)
                    (not main@%_8_0))
                (=> (and main@tailrecurse.i4.preheader_0 main@tailrecurse.i_0)
                    (= main@%xs.tr.ph.i14.lcssa_0 main@%xs.tr.ph.i14_0))
                (=> (and main@tailrecurse.i4.preheader_0 main@tailrecurse.i_0)
                    (= main@%xs.tr.ph.i14.lcssa_1 main@%xs.tr.ph.i14.lcssa_0))
                (=> main@tailrecurse.i4.preheader_0 a!1)
                (=> main@tailrecurse.i4.preheader_0
                    (or (<= main@%xs.tr.ph.i14.lcssa_1 0) (> main@%_15_0 0)))
                (=> main@tailrecurse.i4.preheader_0 (= main@%_16_0 @nd_0))
                (=> main@tailrecurse.i4.preheader_0
                    (= main@%_18_0 (select main@%_3_0 main@%_15_0)))
                (=> main@tailrecurse.i4.preheader_0
                    (= main@%_19_0 (+ main@%_18_0 1)))
                (=> main@tailrecurse.i4.preheader_0
                    (= main@%_20_0 (store main@%_3_0 main@%_15_0 main@%_19_0)))
                a!2
                (=> main@tailrecurse.i4.preheader_0 a!3)
                (=> main@tailrecurse.i4.preheader_0
                    (or (<= main@%xs.tr.ph.i14.lcssa_1 0) (> main@%_22_0 0)))
                (=> main@tailrecurse.i4.preheader_0 a!4)
                (=> main@tailrecurse.i4.preheader_0
                    (or (<= main@%xs.tr.ph.i14.lcssa_1 0) (> main@%_23_0 0)))
                (=> main@tailrecurse.i4.preheader_0
                    (= main@%_24_0 (ite main@%_21_0 main@%_22_0 main@%_23_0)))
                (=> main@tailrecurse.i4.preheader_0 (= main@%_25_0 main@%_24_0))
                (=> main@tailrecurse.i4_0
                    (and main@tailrecurse.i4_0 main@tailrecurse.i4.preheader_0))
                main@tailrecurse.i4_0
                (=> (and main@tailrecurse.i4_0 main@tailrecurse.i4.preheader_0)
                    (= main@%xs.tr.ph.i113_0 main@%_25_0))
                (=> (and main@tailrecurse.i4_0 main@tailrecurse.i4.preheader_0)
                    (= main@%xs.tr.ph.i113_1 main@%xs.tr.ph.i113_0)))))
  (=> a!5
      (main@tailrecurse.i4
        @nd_0
        main@%xs.tr.ph.i113_1
        main@%_20_0
        main@%_2_0
        main@%_4_0)))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ main@%xs.tr.ph.i14_0 (* 0 12)) 8)))
      (a!2 (= main@%_13_0 (+ (+ main@%xs.tr.ph.i14_0 (* 0 12)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%xs.tr.ph.i14_0
                  main@%_3_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (= main@%_7_0 0))
                (=> main@tailrecurse.outer.backedge.i_0
                    (and main@tailrecurse.outer.backedge.i_0
                         main@tailrecurse.i_0))
                (=> (and main@tailrecurse.outer.backedge.i_0
                         main@tailrecurse.i_0)
                    main@%_8_0)
                (=> main@tailrecurse.outer.backedge.i_0 (= main@%_9_0 @nd_0))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%_11_0 (= main@%_10_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0 a!1)
                (=> main@tailrecurse.outer.backedge.i_0
                    (or (<= main@%xs.tr.ph.i14_0 0) (> main@%_12_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0 a!2)
                (=> main@tailrecurse.outer.backedge.i_0
                    (or (<= main@%xs.tr.ph.i14_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%xs.tr.ph.be.in.i_0
                       (ite main@%_11_0 main@%_12_0 main@%_13_0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%xs.tr.ph.be.i_0
                       (select main@%_3_0 main@%xs.tr.ph.be.in.i_0)))
                (=> main@tailrecurse.outer.backedge.i_0
                    (= main@%_14_0 (= main@%xs.tr.ph.be.i_0 0)))
                (=> main@tailrecurse.us.i.preheader.loopexit_0
                    (and main@tailrecurse.us.i.preheader.loopexit_0
                         main@tailrecurse.outer.backedge.i_0))
                (=> (and main@tailrecurse.us.i.preheader.loopexit_0
                         main@tailrecurse.outer.backedge.i_0)
                    main@%_14_0)
                (=> main@tailrecurse.us.i.preheader_0
                    (and main@tailrecurse.us.i.preheader_0
                         main@tailrecurse.us.i.preheader.loopexit_0))
                (=> main@tailrecurse.us.i_0
                    (and main@tailrecurse.us.i_0
                         main@tailrecurse.us.i.preheader_0))
                main@tailrecurse.us.i_0)))
  (=> a!3 main@tailrecurse.us.i))))
(rule (let ((a!1 (= main@%_32_0 (+ (+ main@%xs.tr.ph.i113_0 (* 0 12)) 8)))
      (a!2 (= main@%_33_0 (+ (+ main@%xs.tr.ph.i113_0 (* 0 12)) 4))))
(let ((a!3 (and (main@tailrecurse.i4
                  @nd_0
                  main@%xs.tr.ph.i113_0
                  main@%_20_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_26_0 @nd_0)
                (= main@%_28_0 (= main@%_27_0 0))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (and main@tailrecurse.outer.backedge.i9_0
                         main@tailrecurse.i4_0))
                (=> (and main@tailrecurse.outer.backedge.i9_0
                         main@tailrecurse.i4_0)
                    main@%_28_0)
                (=> main@tailrecurse.outer.backedge.i9_0 (= main@%_29_0 @nd_0))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%_31_0 (= main@%_30_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0 a!1)
                (=> main@tailrecurse.outer.backedge.i9_0
                    (or (<= main@%xs.tr.ph.i113_0 0) (> main@%_32_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0 a!2)
                (=> main@tailrecurse.outer.backedge.i9_0
                    (or (<= main@%xs.tr.ph.i113_0 0) (> main@%_33_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%xs.tr.ph.be.in.i7_0
                       (ite main@%_31_0 main@%_32_0 main@%_33_0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%xs.tr.ph.be.i8_0
                       (select main@%_20_0 main@%xs.tr.ph.be.in.i7_0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%_34_0 (= main@%xs.tr.ph.be.i8_0 0)))
                (=> main@tailrecurse.i4_1
                    (and main@tailrecurse.i4_1
                         main@tailrecurse.outer.backedge.i9_0))
                main@tailrecurse.i4_1
                (=> (and main@tailrecurse.i4_1
                         main@tailrecurse.outer.backedge.i9_0)
                    (not main@%_34_0))
                (=> (and main@tailrecurse.i4_1
                         main@tailrecurse.outer.backedge.i9_0)
                    (= main@%xs.tr.ph.i113_1 main@%xs.tr.ph.be.i8_0))
                (=> (and main@tailrecurse.i4_1
                         main@tailrecurse.outer.backedge.i9_0)
                    (= main@%xs.tr.ph.i113_2 main@%xs.tr.ph.i113_1)))))
  (=> a!3
      (main@tailrecurse.i4
        @nd_0
        main@%xs.tr.ph.i113_2
        main@%_20_0
        main@%_2_0
        main@%_4_0)))))
(rule (let ((a!1 (=> main@some.exit10_0
               (= main@%_35_0 (+ main@%xs.tr.ph.i113.lcssa_1 (* 0 12) 0)))))
(let ((a!2 (and (main@tailrecurse.i4
                  @nd_0
                  main@%xs.tr.ph.i113_0
                  main@%_20_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_26_0 @nd_0)
                (= main@%_28_0 (= main@%_27_0 0))
                (=> main@some.exit10_0
                    (and main@some.exit10_0 main@tailrecurse.i4_0))
                (=> (and main@some.exit10_0 main@tailrecurse.i4_0)
                    (not main@%_28_0))
                (=> (and main@some.exit10_0 main@tailrecurse.i4_0)
                    (= main@%xs.tr.ph.i113.lcssa_0 main@%xs.tr.ph.i113_0))
                (=> (and main@some.exit10_0 main@tailrecurse.i4_0)
                    (= main@%xs.tr.ph.i113.lcssa_1 main@%xs.tr.ph.i113.lcssa_0))
                a!1
                (=> main@some.exit10_0
                    (or (<= main@%xs.tr.ph.i113.lcssa_1 0) (> main@%_35_0 0)))
                (=> main@some.exit10_0 (= main@%_36_0 @nd_0))
                (=> main@some.exit10_0
                    (= main@%_38_0 (select main@%_20_0 main@%_35_0)))
                (=> main@some.exit10_0 (= main@%_39_0 (+ main@%_38_0 1)))
                (=> main@some.exit10_0
                    (= main@%_40_0 (store main@%_20_0 main@%_35_0 main@%_39_0)))
                (sum main@some.exit10_0
                     false
                     false
                     main@%_40_0
                     main@%_41_0
                     main@%_2_0
                     main@%_42_0)
                (=> main@some.exit10_0 (= main@%_43_0 (+ main@%_4_0 2)))
                (=> main@some.exit10_0
                    (= main@%_44_0 (> main@%_42_0 main@%_43_0)))
                (=> main@some.exit10_0 (not main@%_44_0))
                (=> main@some.exit10.split_0
                    (and main@some.exit10.split_0 main@some.exit10_0))
                main@some.exit10.split_0)))
  (=> a!2 main@some.exit10.split))))
(rule (let ((a!1 (= main@%_32_0 (+ (+ main@%xs.tr.ph.i113_0 (* 0 12)) 8)))
      (a!2 (= main@%_33_0 (+ (+ main@%xs.tr.ph.i113_0 (* 0 12)) 4))))
(let ((a!3 (and (main@tailrecurse.i4
                  @nd_0
                  main@%xs.tr.ph.i113_0
                  main@%_20_0
                  main@%_2_0
                  main@%_4_0)
                true
                (= main@%_26_0 @nd_0)
                (= main@%_28_0 (= main@%_27_0 0))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (and main@tailrecurse.outer.backedge.i9_0
                         main@tailrecurse.i4_0))
                (=> (and main@tailrecurse.outer.backedge.i9_0
                         main@tailrecurse.i4_0)
                    main@%_28_0)
                (=> main@tailrecurse.outer.backedge.i9_0 (= main@%_29_0 @nd_0))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%_31_0 (= main@%_30_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0 a!1)
                (=> main@tailrecurse.outer.backedge.i9_0
                    (or (<= main@%xs.tr.ph.i113_0 0) (> main@%_32_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0 a!2)
                (=> main@tailrecurse.outer.backedge.i9_0
                    (or (<= main@%xs.tr.ph.i113_0 0) (> main@%_33_0 0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%xs.tr.ph.be.in.i7_0
                       (ite main@%_31_0 main@%_32_0 main@%_33_0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%xs.tr.ph.be.i8_0
                       (select main@%_20_0 main@%xs.tr.ph.be.in.i7_0)))
                (=> main@tailrecurse.outer.backedge.i9_0
                    (= main@%_34_0 (= main@%xs.tr.ph.be.i8_0 0)))
                (=> main@tailrecurse.us.i3.preheader_0
                    (and main@tailrecurse.us.i3.preheader_0
                         main@tailrecurse.outer.backedge.i9_0))
                (=> (and main@tailrecurse.us.i3.preheader_0
                         main@tailrecurse.outer.backedge.i9_0)
                    main@%_34_0)
                (=> main@tailrecurse.us.i3_0
                    (and main@tailrecurse.us.i3_0
                         main@tailrecurse.us.i3.preheader_0))
                main@tailrecurse.us.i3_0)))
  (=> a!3 main@tailrecurse.us.i3))))
(rule (=> (and main@tailrecurse.us.i3
         true
         (=> main@tailrecurse.us.i3_1
             (and main@tailrecurse.us.i3_1 main@tailrecurse.us.i3_0))
         main@tailrecurse.us.i3_1)
    main@tailrecurse.us.i3))
(rule (=> (and main@tailrecurse.us.i
         true
         (=> main@tailrecurse.us.i_1
             (and main@tailrecurse.us.i_1 main@tailrecurse.us.i_0))
         main@tailrecurse.us.i_1)
    main@tailrecurse.us.i))
(query main@some.exit10.split)

