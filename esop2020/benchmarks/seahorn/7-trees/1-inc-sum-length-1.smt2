(set-info :original "7-trees/1-inc-sum-length-1.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_tree@_1 ((Array Int Int) Int ))
(declare-rel nd_tree@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_tree (Bool Bool Bool (Array Int Int) Int ))
(declare-rel sum@_1 ((Array Int Int) Int ))
(declare-rel sum@tailrecurse ((Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel sum@tailrecurse._crit_edge.split ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel sum (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel size@_1 ((Array Int Int) Int ))
(declare-rel size@tailrecurse ((Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel size@tailrecurse._crit_edge.split ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel size (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel inc@_1 ((Array Int Int) Int ))
(declare-rel inc@tailrecurse ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel inc@tailrecurse._crit_edge ((Array Int Int) (Array Int Int) Int ))
(declare-rel inc (Bool Bool Bool (Array Int Int) (Array Int Int) Int ))
(declare-rel main@entry ())
(declare-rel main@entry.split ())
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
(declare-var size@%_call_0 Int )
(declare-var size@%_5_0 Int )
(declare-var size@%_7_0 Int )
(declare-var size@%_call1_0 Int )
(declare-var size@%_10_0 Int )
(declare-var size@%_br3_0 Bool )
(declare-var size@%.lcssa_1 Int )
(declare-var size@%shadow.mem.0_2 (Array Int Int) )
(declare-var size@%xs.tr2_2 Int )
(declare-var size@%accumulator.tr1_2 Int )
(declare-var size@%_br_0 Bool )
(declare-var size@%_tail_0 (Array Int Int) )
(declare-var size@%shadow.mem.1_0 (Array Int Int) )
(declare-var size@%xs_0 Int )
(declare-var size@%accumulator.tr.lcssa_0 Int )
(declare-var size@_1_0 Bool )
(declare-var size@tailrecurse.preheader_0 Bool )
(declare-var size@tailrecurse_0 Bool )
(declare-var size@%shadow.mem.0_0 (Array Int Int) )
(declare-var size@%xs.tr2_0 Int )
(declare-var size@%accumulator.tr1_0 Int )
(declare-var size@%shadow.mem.0_1 (Array Int Int) )
(declare-var size@%xs.tr2_1 Int )
(declare-var size@%accumulator.tr1_1 Int )
(declare-var size@tailrecurse._crit_edge_0 Bool )
(declare-var size@%shadow.mem.1_1 (Array Int Int) )
(declare-var size@%accumulator.tr.lcssa_1 Int )
(declare-var size@tailrecurse._crit_edge.split_0 Bool )
(declare-var size@%_6_0 (Array Int Int) )
(declare-var size@%_9_0 Int )
(declare-var size@%_tail2_0 Int )
(declare-var size@tailrecurse_1 Bool )
(declare-var size@tailrecurse._crit_edge.loopexit_0 Bool )
(declare-var size@%.lcssa_0 Int )
(declare-var inc@%_call_0 Int )
(declare-var inc@%_5_0 Int )
(declare-var inc@%_tail1_0 (Array Int Int) )
(declare-var inc@%_call2_0 Int )
(declare-var inc@%_8_0 Int )
(declare-var inc@%_9_0 Int )
(declare-var inc@%_call3_0 Int )
(declare-var inc@%_br5_0 Bool )
(declare-var inc@%shadow.mem.0_2 (Array Int Int) )
(declare-var inc@%xs.tr1_2 Int )
(declare-var inc@%_br_0 Bool )
(declare-var inc@%_tail_0 (Array Int Int) )
(declare-var inc@%shadow.mem.1_0 (Array Int Int) )
(declare-var inc@%xs_0 Int )
(declare-var inc@_1_0 Bool )
(declare-var inc@tailrecurse.preheader_0 Bool )
(declare-var inc@tailrecurse_0 Bool )
(declare-var inc@%shadow.mem.0_0 (Array Int Int) )
(declare-var inc@%xs.tr1_0 Int )
(declare-var inc@%shadow.mem.0_1 (Array Int Int) )
(declare-var inc@%xs.tr1_1 Int )
(declare-var inc@tailrecurse._crit_edge_0 Bool )
(declare-var inc@%shadow.mem.1_1 (Array Int Int) )
(declare-var inc@%_store_0 (Array Int Int) )
(declare-var inc@%_tail4_0 Int )
(declare-var inc@tailrecurse_1 Bool )
(declare-var inc@tailrecurse._crit_edge.loopexit_0 Bool )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 (Array Int Int) )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 (Array Int Int) )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 (Array Int Int) )
(declare-var main@%_8_0 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@entry.split_0 Bool )
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
(rule (size true
      true
      true
      size@%_tail_0
      size@%shadow.mem.1_0
      size@%xs_0
      size@%accumulator.tr.lcssa_0))
(rule (size false
      true
      true
      size@%_tail_0
      size@%shadow.mem.1_0
      size@%xs_0
      size@%accumulator.tr.lcssa_0))
(rule (size false
      false
      false
      size@%_tail_0
      size@%shadow.mem.1_0
      size@%xs_0
      size@%accumulator.tr.lcssa_0))
(rule (size@_1 size@%_tail_0 size@%xs_0))
(rule (=> (and (size@_1 size@%_tail_0 size@%xs_0)
         true
         (= size@%_br_0 (= size@%xs_0 0))
         (=> size@tailrecurse.preheader_0
             (and size@tailrecurse.preheader_0 size@_1_0))
         (=> (and size@tailrecurse.preheader_0 size@_1_0) (not size@%_br_0))
         (=> size@tailrecurse_0
             (and size@tailrecurse_0 size@tailrecurse.preheader_0))
         size@tailrecurse_0
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%shadow.mem.0_0 size@%_tail_0))
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%xs.tr2_0 size@%xs_0))
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%accumulator.tr1_0 0))
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%shadow.mem.0_1 size@%shadow.mem.0_0))
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%xs.tr2_1 size@%xs.tr2_0))
         (=> (and size@tailrecurse_0 size@tailrecurse.preheader_0)
             (= size@%accumulator.tr1_1 size@%accumulator.tr1_0)))
    (size@tailrecurse size@%_tail_0
                      size@%xs.tr2_1
                      size@%shadow.mem.0_1
                      size@%accumulator.tr1_1
                      size@%xs_0)))
(rule (=> (and (size@_1 size@%_tail_0 size@%xs_0)
         true
         (= size@%_br_0 (= size@%xs_0 0))
         (=> size@tailrecurse._crit_edge_0
             (and size@tailrecurse._crit_edge_0 size@_1_0))
         (=> (and size@tailrecurse._crit_edge_0 size@_1_0) size@%_br_0)
         (=> (and size@tailrecurse._crit_edge_0 size@_1_0)
             (= size@%shadow.mem.1_0 size@%_tail_0))
         (=> (and size@tailrecurse._crit_edge_0 size@_1_0)
             (= size@%accumulator.tr.lcssa_0 0))
         (=> (and size@tailrecurse._crit_edge_0 size@_1_0)
             (= size@%shadow.mem.1_1 size@%shadow.mem.1_0))
         (=> (and size@tailrecurse._crit_edge_0 size@_1_0)
             (= size@%accumulator.tr.lcssa_1 size@%accumulator.tr.lcssa_0))
         (=> size@tailrecurse._crit_edge.split_0
             (and size@tailrecurse._crit_edge.split_0
                  size@tailrecurse._crit_edge_0))
         size@tailrecurse._crit_edge.split_0)
    (size@tailrecurse._crit_edge.split
      size@%_tail_0
      size@%shadow.mem.1_1
      size@%accumulator.tr.lcssa_1
      size@%xs_0)))
(rule (let ((a!1 (= size@%_call_0 (+ (+ size@%xs.tr2_0 (* 0 12)) 4)))
      (a!2 (= size@%_call1_0 (+ (+ size@%xs.tr2_0 (* 0 12)) 8))))
  (=> (and (size@tailrecurse size@%_tail_0
                             size@%xs.tr2_0
                             size@%shadow.mem.0_0
                             size@%accumulator.tr1_0
                             size@%xs_0)
           true
           a!1
           (or (<= size@%xs.tr2_0 0) (> size@%_call_0 0))
           (> size@%xs.tr2_0 0)
           (= size@%_5_0 (select size@%shadow.mem.0_0 size@%_call_0))
           (size true
                 false
                 false
                 size@%shadow.mem.0_0
                 size@%_6_0
                 size@%_5_0
                 size@%_7_0)
           a!2
           (or (<= size@%xs.tr2_0 0) (> size@%_call1_0 0))
           (> size@%xs.tr2_0 0)
           (= size@%_9_0 (select size@%_6_0 size@%_call1_0))
           (= size@%_10_0 (+ size@%accumulator.tr1_0 1))
           (= size@%_tail2_0 (+ size@%_10_0 size@%_7_0))
           (= size@%_br3_0 (= size@%_9_0 0))
           (=> size@tailrecurse_1 (and size@tailrecurse_1 size@tailrecurse_0))
           size@tailrecurse_1
           (=> (and size@tailrecurse_1 size@tailrecurse_0) (not size@%_br3_0))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%shadow.mem.0_1 size@%_6_0))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%xs.tr2_1 size@%_9_0))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%accumulator.tr1_1 size@%_tail2_0))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%shadow.mem.0_2 size@%shadow.mem.0_1))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%xs.tr2_2 size@%xs.tr2_1))
           (=> (and size@tailrecurse_1 size@tailrecurse_0)
               (= size@%accumulator.tr1_2 size@%accumulator.tr1_1)))
      (size@tailrecurse size@%_tail_0
                        size@%xs.tr2_2
                        size@%shadow.mem.0_2
                        size@%accumulator.tr1_2
                        size@%xs_0))))
(rule (let ((a!1 (= size@%_call_0 (+ (+ size@%xs.tr2_0 (* 0 12)) 4)))
      (a!2 (= size@%_call1_0 (+ (+ size@%xs.tr2_0 (* 0 12)) 8))))
  (=> (and (size@tailrecurse size@%_tail_0
                             size@%xs.tr2_0
                             size@%shadow.mem.0_0
                             size@%accumulator.tr1_0
                             size@%xs_0)
           true
           a!1
           (or (<= size@%xs.tr2_0 0) (> size@%_call_0 0))
           (> size@%xs.tr2_0 0)
           (= size@%_5_0 (select size@%shadow.mem.0_0 size@%_call_0))
           (size true
                 false
                 false
                 size@%shadow.mem.0_0
                 size@%_6_0
                 size@%_5_0
                 size@%_7_0)
           a!2
           (or (<= size@%xs.tr2_0 0) (> size@%_call1_0 0))
           (> size@%xs.tr2_0 0)
           (= size@%_9_0 (select size@%_6_0 size@%_call1_0))
           (= size@%_10_0 (+ size@%accumulator.tr1_0 1))
           (= size@%_tail2_0 (+ size@%_10_0 size@%_7_0))
           (= size@%_br3_0 (= size@%_9_0 0))
           (=> size@tailrecurse._crit_edge.loopexit_0
               (and size@tailrecurse._crit_edge.loopexit_0 size@tailrecurse_0))
           (=> (and size@tailrecurse._crit_edge.loopexit_0 size@tailrecurse_0)
               size@%_br3_0)
           (=> (and size@tailrecurse._crit_edge.loopexit_0 size@tailrecurse_0)
               (= size@%.lcssa_0 size@%_tail2_0))
           (=> (and size@tailrecurse._crit_edge.loopexit_0 size@tailrecurse_0)
               (= size@%.lcssa_1 size@%.lcssa_0))
           (=> size@tailrecurse._crit_edge_0
               (and size@tailrecurse._crit_edge_0
                    size@tailrecurse._crit_edge.loopexit_0))
           (=> (and size@tailrecurse._crit_edge_0
                    size@tailrecurse._crit_edge.loopexit_0)
               (= size@%shadow.mem.1_0 size@%_6_0))
           (=> (and size@tailrecurse._crit_edge_0
                    size@tailrecurse._crit_edge.loopexit_0)
               (= size@%accumulator.tr.lcssa_0 size@%.lcssa_1))
           (=> (and size@tailrecurse._crit_edge_0
                    size@tailrecurse._crit_edge.loopexit_0)
               (= size@%shadow.mem.1_1 size@%shadow.mem.1_0))
           (=> (and size@tailrecurse._crit_edge_0
                    size@tailrecurse._crit_edge.loopexit_0)
               (= size@%accumulator.tr.lcssa_1 size@%accumulator.tr.lcssa_0))
           (=> size@tailrecurse._crit_edge.split_0
               (and size@tailrecurse._crit_edge.split_0
                    size@tailrecurse._crit_edge_0))
           size@tailrecurse._crit_edge.split_0)
      (size@tailrecurse._crit_edge.split
        size@%_tail_0
        size@%shadow.mem.1_1
        size@%accumulator.tr.lcssa_1
        size@%xs_0))))
(rule (=> (size@tailrecurse._crit_edge.split
      size@%_tail_0
      size@%shadow.mem.1_0
      size@%accumulator.tr.lcssa_0
      size@%xs_0)
    (size true
          false
          false
          size@%_tail_0
          size@%shadow.mem.1_0
          size@%xs_0
          size@%accumulator.tr.lcssa_0)))
(rule (inc true true true inc@%_tail_0 inc@%shadow.mem.1_0 inc@%xs_0))
(rule (inc false true true inc@%_tail_0 inc@%shadow.mem.1_0 inc@%xs_0))
(rule (inc false false false inc@%_tail_0 inc@%shadow.mem.1_0 inc@%xs_0))
(rule (inc@_1 inc@%_tail_0 inc@%xs_0))
(rule (=> (and (inc@_1 inc@%_tail_0 inc@%xs_0)
         true
         (= inc@%_br_0 (= inc@%xs_0 0))
         (=> inc@tailrecurse.preheader_0
             (and inc@tailrecurse.preheader_0 inc@_1_0))
         (=> (and inc@tailrecurse.preheader_0 inc@_1_0) (not inc@%_br_0))
         (=> inc@tailrecurse_0
             (and inc@tailrecurse_0 inc@tailrecurse.preheader_0))
         inc@tailrecurse_0
         (=> (and inc@tailrecurse_0 inc@tailrecurse.preheader_0)
             (= inc@%shadow.mem.0_0 inc@%_tail_0))
         (=> (and inc@tailrecurse_0 inc@tailrecurse.preheader_0)
             (= inc@%xs.tr1_0 inc@%xs_0))
         (=> (and inc@tailrecurse_0 inc@tailrecurse.preheader_0)
             (= inc@%shadow.mem.0_1 inc@%shadow.mem.0_0))
         (=> (and inc@tailrecurse_0 inc@tailrecurse.preheader_0)
             (= inc@%xs.tr1_1 inc@%xs.tr1_0)))
    (inc@tailrecurse inc@%_tail_0 inc@%xs.tr1_1 inc@%shadow.mem.0_1 inc@%xs_0)))
(rule (=> (and (inc@_1 inc@%_tail_0 inc@%xs_0)
         true
         (= inc@%_br_0 (= inc@%xs_0 0))
         (=> inc@tailrecurse._crit_edge_0
             (and inc@tailrecurse._crit_edge_0 inc@_1_0))
         inc@tailrecurse._crit_edge_0
         (=> (and inc@tailrecurse._crit_edge_0 inc@_1_0) inc@%_br_0)
         (=> (and inc@tailrecurse._crit_edge_0 inc@_1_0)
             (= inc@%shadow.mem.1_0 inc@%_tail_0))
         (=> (and inc@tailrecurse._crit_edge_0 inc@_1_0)
             (= inc@%shadow.mem.1_1 inc@%shadow.mem.1_0)))
    (inc@tailrecurse._crit_edge inc@%_tail_0 inc@%shadow.mem.1_1 inc@%xs_0)))
(rule (let ((a!1 (= inc@%_call_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 4)))
      (a!2 (= inc@%_call2_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 0)))
      (a!3 (= inc@%_call3_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 8))))
  (=> (and (inc@tailrecurse inc@%_tail_0
                            inc@%xs.tr1_0
                            inc@%shadow.mem.0_0
                            inc@%xs_0)
           true
           a!1
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call_0 0))
           (> inc@%xs.tr1_0 0)
           (= inc@%_5_0 (select inc@%shadow.mem.0_0 inc@%_call_0))
           (inc true false false inc@%shadow.mem.0_0 inc@%_tail1_0 inc@%_5_0)
           a!2
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call2_0 0))
           (= inc@%_8_0 (select inc@%_tail1_0 inc@%_call2_0))
           (= inc@%_9_0 (+ inc@%_8_0 1))
           (= inc@%_store_0 (store inc@%_tail1_0 inc@%_call2_0 inc@%_9_0))
           a!3
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call3_0 0))
           (> inc@%xs.tr1_0 0)
           (= inc@%_tail4_0 (select inc@%_store_0 inc@%_call3_0))
           (= inc@%_br5_0 (= inc@%_tail4_0 0))
           (=> inc@tailrecurse_1 (and inc@tailrecurse_1 inc@tailrecurse_0))
           inc@tailrecurse_1
           (=> (and inc@tailrecurse_1 inc@tailrecurse_0) (not inc@%_br5_0))
           (=> (and inc@tailrecurse_1 inc@tailrecurse_0)
               (= inc@%shadow.mem.0_1 inc@%_store_0))
           (=> (and inc@tailrecurse_1 inc@tailrecurse_0)
               (= inc@%xs.tr1_1 inc@%_tail4_0))
           (=> (and inc@tailrecurse_1 inc@tailrecurse_0)
               (= inc@%shadow.mem.0_2 inc@%shadow.mem.0_1))
           (=> (and inc@tailrecurse_1 inc@tailrecurse_0)
               (= inc@%xs.tr1_2 inc@%xs.tr1_1)))
      (inc@tailrecurse inc@%_tail_0 inc@%xs.tr1_2 inc@%shadow.mem.0_2 inc@%xs_0))))
(rule (let ((a!1 (= inc@%_call_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 4)))
      (a!2 (= inc@%_call2_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 0)))
      (a!3 (= inc@%_call3_0 (+ (+ inc@%xs.tr1_0 (* 0 12)) 8))))
  (=> (and (inc@tailrecurse inc@%_tail_0
                            inc@%xs.tr1_0
                            inc@%shadow.mem.0_0
                            inc@%xs_0)
           true
           a!1
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call_0 0))
           (> inc@%xs.tr1_0 0)
           (= inc@%_5_0 (select inc@%shadow.mem.0_0 inc@%_call_0))
           (inc true false false inc@%shadow.mem.0_0 inc@%_tail1_0 inc@%_5_0)
           a!2
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call2_0 0))
           (= inc@%_8_0 (select inc@%_tail1_0 inc@%_call2_0))
           (= inc@%_9_0 (+ inc@%_8_0 1))
           (= inc@%_store_0 (store inc@%_tail1_0 inc@%_call2_0 inc@%_9_0))
           a!3
           (or (<= inc@%xs.tr1_0 0) (> inc@%_call3_0 0))
           (> inc@%xs.tr1_0 0)
           (= inc@%_tail4_0 (select inc@%_store_0 inc@%_call3_0))
           (= inc@%_br5_0 (= inc@%_tail4_0 0))
           (=> inc@tailrecurse._crit_edge.loopexit_0
               (and inc@tailrecurse._crit_edge.loopexit_0 inc@tailrecurse_0))
           (=> (and inc@tailrecurse._crit_edge.loopexit_0 inc@tailrecurse_0)
               inc@%_br5_0)
           (=> inc@tailrecurse._crit_edge_0
               (and inc@tailrecurse._crit_edge_0
                    inc@tailrecurse._crit_edge.loopexit_0))
           inc@tailrecurse._crit_edge_0
           (=> (and inc@tailrecurse._crit_edge_0
                    inc@tailrecurse._crit_edge.loopexit_0)
               (= inc@%shadow.mem.1_0 inc@%_store_0))
           (=> (and inc@tailrecurse._crit_edge_0
                    inc@tailrecurse._crit_edge.loopexit_0)
               (= inc@%shadow.mem.1_1 inc@%shadow.mem.1_0)))
      (inc@tailrecurse._crit_edge inc@%_tail_0 inc@%shadow.mem.1_1 inc@%xs_0))))
(rule (=> (inc@tailrecurse._crit_edge inc@%_tail_0 inc@%shadow.mem.1_0 inc@%xs_0)
    (inc true false false inc@%_tail_0 inc@%shadow.mem.1_0 inc@%xs_0)))
(rule main@entry)
(rule (=> (and main@entry
         true
         (nd_tree true false false main@%_1_0 main@%_2_0)
         (sum true false false main@%_1_0 main@%_3_0 main@%_2_0 main@%_4_0)
         (size true false false main@%_3_0 main@%_5_0 main@%_2_0 main@%_6_0)
         (inc true false false main@%_5_0 main@%_7_0 main@%_2_0)
         (sum true false false main@%_7_0 main@%_8_0 main@%_2_0 main@%_9_0)
         (= main@%_10_0 (+ main@%_6_0 main@%_4_0))
         (= main@%_11_0 (> main@%_9_0 main@%_10_0))
         (not main@%_11_0)
         (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
         main@entry.split_0)
    main@entry.split))
(query main@entry.split)

