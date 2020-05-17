(set-info :original "3-inc-max/inc-max-3-repeat-unsafe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int Int Int Int (Array Int Int) Int ))
(declare-rel main@inc_max_repeat.exit.split ())
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%..i.i_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%.0.4.pre.lcssa_1 Int )
(declare-var main@%.0..pre.lcssa_1 Int )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%.0.2_2 Int )
(declare-var main@%.0.6_2 Int )
(declare-var main@%.tr3.i_2 Int )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var @nd_0 Int )
(declare-var main@%.0.sroa_cast3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 (Array Int Int) )
(declare-var main@.lr.ph.i_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.0.2_0 Int )
(declare-var main@%.0.6_0 Int )
(declare-var main@%.tr3.i_0 Int )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.0.2_1 Int )
(declare-var main@%.0.6_1 Int )
(declare-var main@%.tr3.i_1 Int )
(declare-var main@inc_max_repeat.exit_0 Bool )
(declare-var main@%.0._0 Int )
(declare-var main@%.0.4_0 Int )
(declare-var main@%.0._1 Int )
(declare-var main@%.0.4_1 Int )
(declare-var main@inc_max_repeat.exit.split_0 Bool )
(declare-var main@%_15_0 (Array Int Int) )
(declare-var main@%_16_0 Int )
(declare-var main@%.0.4.pre_0 Int )
(declare-var main@%.0..pre_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@inc_max_repeat.exit.loopexit_0 Bool )
(declare-var main@%.0.4.pre.lcssa_0 Int )
(declare-var main@%.0..pre.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (> main@%_1_0 0)
         (> main@%_2_0 0)
         (distinct main@%_1_0 main@%_2_0) ; modify
         (= main@%_3_0 @nd_0)
         (= main@%.0.sroa_cast3_0 main@%_1_0)
         (= main@%_5_0 @nd_0)
         (= main@%_7_0 (store main@%_0_0 main@%_1_0 main@%_6_0))
         (= main@%.0.sroa_cast_0 main@%_2_0)
         (= main@%_8_0 @nd_0)
         (= main@%_10_0 (store main@%_7_0 main@%_2_0 main@%_9_0))
         (= main@%_11_0 (= main@%_4_0 0))
         (=> main@.lr.ph.i_0 (and main@.lr.ph.i_0 main@entry_0))
         (=> (and main@.lr.ph.i_0 main@entry_0) (not main@%_11_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@.lr.ph.i_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%shadow.mem.0_0 main@%_10_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.0.2_0 main@%_9_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.0.6_0 main@%_6_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.tr3.i_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.0.2_1 main@%.0.2_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.0.6_1 main@%.0.6_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.tr3.i_1 main@%.tr3.i_0)))
    (main@tailrecurse.i
      main@%_4_0
      main@%.0.6_1
      main@%.0.2_1
      main@%_2_0
      main@%_1_0
      main@%shadow.mem.0_1
      main@%.tr3.i_1)))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (distinct main@%_1_0 main@%_2_0) ; modify
                (= main@%_3_0 @nd_0)
                (= main@%.0.sroa_cast3_0 main@%_1_0)
                (= main@%_5_0 @nd_0)
                (= main@%_7_0 (store main@%_0_0 main@%_1_0 main@%_6_0))
                (= main@%.0.sroa_cast_0 main@%_2_0)
                (= main@%_8_0 @nd_0)
                (= main@%_10_0 (store main@%_7_0 main@%_2_0 main@%_9_0))
                (= main@%_11_0 (= main@%_4_0 0))
                (=> main@inc_max_repeat.exit_0
                    (and main@inc_max_repeat.exit_0 main@entry_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0) main@%_11_0)
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0._0 main@%_9_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0.4_0 main@%_6_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0._1 main@%.0._0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0.4_1 main@%.0.4_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_18_0 (- main@%.0.4_1 main@%.0._1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_19_0 (> main@%_18_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_19_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_20_0 (- main@%.0._1 main@%.0.4_1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_21_0 (> main@%_20_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_21_0))
                (=> main@inc_max_repeat.exit.split_0
                    (and main@inc_max_repeat.exit.split_0
                         main@inc_max_repeat.exit_0))
                main@inc_max_repeat.exit.split_0)))
  (=> a!1 main@inc_max_repeat.exit.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_4_0
           main@%.0.6_0
           main@%.0.2_0
           main@%_2_0
           main@%_1_0
           main@%shadow.mem.0_0
           main@%.tr3.i_0)
         true
         (= main@%_12_0 (< main@%.0.6_0 main@%.0.2_0))
         (= main@%..i.i_0 (ite main@%_12_0 main@%_2_0 main@%_1_0))
         (= main@%_13_0 (select main@%shadow.mem.0_0 main@%..i.i_0))
         (= main@%_14_0 (+ main@%_13_0 1))
         (= main@%_15_0 (store main@%shadow.mem.0_0 main@%..i.i_0 main@%_14_0))
         (= main@%_16_0 (+ main@%.tr3.i_0 (- 1)))
         (= main@%_17_0 (= main@%_16_0 0))
         (= main@%.0.4.pre_0 (select main@%_15_0 main@%_1_0))
         (= main@%.0..pre_0 (select main@%_15_0 main@%_2_0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         main@tailrecurse.i_1
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_17_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_1 main@%_15_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.2_1 main@%.0..pre_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.6_1 main@%.0.4.pre_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr3.i_1 main@%_16_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.2_2 main@%.0.2_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.6_2 main@%.0.6_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr3.i_2 main@%.tr3.i_1)))
    (main@tailrecurse.i
      main@%_4_0
      main@%.0.6_2
      main@%.0.2_2
      main@%_2_0
      main@%_1_0
      main@%shadow.mem.0_2
      main@%.tr3.i_2)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%.0.6_0
                  main@%.0.2_0
                  main@%_2_0
                  main@%_1_0
                  main@%shadow.mem.0_0
                  main@%.tr3.i_0)
                true
                (= main@%_12_0 (< main@%.0.6_0 main@%.0.2_0))
                (= main@%..i.i_0 (ite main@%_12_0 main@%_2_0 main@%_1_0))
                (= main@%_13_0 (select main@%shadow.mem.0_0 main@%..i.i_0))
                (= main@%_14_0 (+ main@%_13_0 1))
                (= main@%_15_0
                   (store main@%shadow.mem.0_0 main@%..i.i_0 main@%_14_0))
                (= main@%_16_0 (+ main@%.tr3.i_0 (- 1)))
                (= main@%_17_0 (= main@%_16_0 0))
                (= main@%.0.4.pre_0 (select main@%_15_0 main@%_1_0))
                (= main@%.0..pre_0 (select main@%_15_0 main@%_2_0))
                (=> main@inc_max_repeat.exit.loopexit_0
                    (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0))
                (=> (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0)
                    main@%_17_0)
                (=> (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0)
                    (= main@%.0.4.pre.lcssa_0 main@%.0.4.pre_0))
                (=> (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0)
                    (= main@%.0..pre.lcssa_0 main@%.0..pre_0))
                (=> (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0)
                    (= main@%.0.4.pre.lcssa_1 main@%.0.4.pre.lcssa_0))
                (=> (and main@inc_max_repeat.exit.loopexit_0
                         main@tailrecurse.i_0)
                    (= main@%.0..pre.lcssa_1 main@%.0..pre.lcssa_0))
                (=> main@inc_max_repeat.exit_0
                    (and main@inc_max_repeat.exit_0
                         main@inc_max_repeat.exit.loopexit_0))
                (=> (and main@inc_max_repeat.exit_0
                         main@inc_max_repeat.exit.loopexit_0)
                    (= main@%.0._0 main@%.0..pre.lcssa_1))
                (=> (and main@inc_max_repeat.exit_0
                         main@inc_max_repeat.exit.loopexit_0)
                    (= main@%.0.4_0 main@%.0.4.pre.lcssa_1))
                (=> (and main@inc_max_repeat.exit_0
                         main@inc_max_repeat.exit.loopexit_0)
                    (= main@%.0._1 main@%.0._0))
                (=> (and main@inc_max_repeat.exit_0
                         main@inc_max_repeat.exit.loopexit_0)
                    (= main@%.0.4_1 main@%.0.4_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_18_0 (- main@%.0.4_1 main@%.0._1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_19_0 (> main@%_18_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_19_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_20_0 (- main@%.0._1 main@%.0.4_1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_21_0 (> main@%_20_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_21_0))
                (=> main@inc_max_repeat.exit.split_0
                    (and main@inc_max_repeat.exit.split_0
                         main@inc_max_repeat.exit_0))
                main@inc_max_repeat.exit.split_0)))
  (=> a!1 main@inc_max_repeat.exit.split)))
(query main@inc_max_repeat.exit.split)

