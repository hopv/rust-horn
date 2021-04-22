(set-info :original "04-inc-max/inc-max-3-repeat-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int Int Int Int (Array Int Int) Int Int ))
(declare-rel main@inc_max_repeat.exit.split ())
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%..i.i_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var @nd_0 Int )
(declare-var main@%.0.sroa_cast2_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%.0.1_2 Int )
(declare-var main@%.0.4_2 Int )
(declare-var main@%.tr3.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.0.1_0 Int )
(declare-var main@%.0.4_0 Int )
(declare-var main@%.tr3.i_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.0.1_1 Int )
(declare-var main@%.0.4_1 Int )
(declare-var main@%.tr3.i_1 Int )
(declare-var main@inc_max_repeat.exit_0 Bool )
(declare-var main@%.0._0 Int )
(declare-var main@%.0.3_0 Int )
(declare-var main@%.0._1 Int )
(declare-var main@%.0.3_1 Int )
(declare-var main@inc_max_repeat.exit.split_0 Bool )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%_13_0 Int )
(declare-var main@%.0.3.pre_0 Int )
(declare-var main@%.0..pre_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (> main@%_1_0 0)
         (> main@%_2_0 0)
         (= main@%_3_0 @nd_0)
         (= main@%.0.sroa_cast2_0 main@%_1_0)
         (= main@%_5_0 @nd_0)
         (= main@%sm_0 (store main@%sm3_0 main@%_1_0 main@%_6_0))
         (= main@%.0.sroa_cast_0 main@%_2_0)
         (= main@%_7_0 @nd_0)
         (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_8_0))
         (= main@%_9_0 (= main@%_4_0 0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (not main@%_9_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0.0_0 main@%sm1_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.0.1_0 main@%_8_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.0.4_0 main@%_6_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.0.1_1 main@%.0.1_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.0.4_1 main@%.0.4_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_1 main@%.tr3.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%_4_0
      main@%.0.4_1
      main@%.0.1_1
      main@%_2_0
      main@%_1_0
      main@%shadow.mem.0.0_1
      main@%.tr3.i_1
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (= main@%_3_0 @nd_0)
                (= main@%.0.sroa_cast2_0 main@%_1_0)
                (= main@%_5_0 @nd_0)
                (= main@%sm_0 (store main@%sm3_0 main@%_1_0 main@%_6_0))
                (= main@%.0.sroa_cast_0 main@%_2_0)
                (= main@%_7_0 @nd_0)
                (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_8_0))
                (= main@%_9_0 (= main@%_4_0 0))
                (=> main@inc_max_repeat.exit_0
                    (and main@inc_max_repeat.exit_0 main@entry_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0) main@%_9_0)
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0._0 main@%_8_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0.3_0 main@%_6_0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0._1 main@%.0._0))
                (=> (and main@inc_max_repeat.exit_0 main@entry_0)
                    (= main@%.0.3_1 main@%.0.3_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_15_0 (- main@%.0.3_1 main@%.0._1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_16_0 (> main@%_15_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_16_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_17_0 (- main@%.0._1 main@%.0.3_1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_18_0 (> main@%_17_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_18_0))
                (=> main@inc_max_repeat.exit.split_0
                    (and main@inc_max_repeat.exit.split_0
                         main@inc_max_repeat.exit_0))
                main@inc_max_repeat.exit.split_0)))
  (=> a!1 main@inc_max_repeat.exit.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_4_0
           main@%.0.4_0
           main@%.0.1_0
           main@%_2_0
           main@%_1_0
           main@%shadow.mem.0.0_0
           main@%.tr3.i_0
           main@%loop.bound_0)
         true
         (= main@%_10_0 (< main@%.0.4_0 main@%.0.1_0))
         (= main@%..i.i_0 (ite main@%_10_0 main@%_2_0 main@%_1_0))
         (= main@%_11_0 (select main@%shadow.mem.0.0_0 main@%..i.i_0))
         (= main@%_12_0 (+ main@%_11_0 1))
         (= main@%sm2_0
            (store main@%shadow.mem.0.0_0 main@%..i.i_0 main@%_12_0))
         (= main@%_13_0 (+ main@%.tr3.i_0 (- 1)))
         (= main@%_14_0 (= main@%_13_0 main@%loop.bound_0))
         (= main@%.0.3.pre_0 (select main@%sm2_0 main@%_1_0))
         (= main@%.0..pre_0 (select main@%sm2_0 main@%_2_0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_14_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_1 main@%sm2_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.1_1 main@%.0..pre_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.4_1 main@%.0.3.pre_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr3.i_1 main@%_13_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.1_2 main@%.0.1_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0.4_2 main@%.0.4_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr3.i_2 main@%.tr3.i_1))
         main@tailrecurse.i_1)
    (main@tailrecurse.i
      main@%_4_0
      main@%.0.4_2
      main@%.0.1_2
      main@%_2_0
      main@%_1_0
      main@%shadow.mem.0.0_2
      main@%.tr3.i_2
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%.0.4_0
                  main@%.0.1_0
                  main@%_2_0
                  main@%_1_0
                  main@%shadow.mem.0.0_0
                  main@%.tr3.i_0
                  main@%loop.bound_0)
                true
                (= main@%_10_0 (< main@%.0.4_0 main@%.0.1_0))
                (= main@%..i.i_0 (ite main@%_10_0 main@%_2_0 main@%_1_0))
                (= main@%_11_0 (select main@%shadow.mem.0.0_0 main@%..i.i_0))
                (= main@%_12_0 (+ main@%_11_0 1))
                (= main@%sm2_0
                   (store main@%shadow.mem.0.0_0 main@%..i.i_0 main@%_12_0))
                (= main@%_13_0 (+ main@%.tr3.i_0 (- 1)))
                (= main@%_14_0 (= main@%_13_0 main@%loop.bound_0))
                (= main@%.0.3.pre_0 (select main@%sm2_0 main@%_1_0))
                (= main@%.0..pre_0 (select main@%sm2_0 main@%_2_0))
                (=> main@inc_max_repeat.exit_0
                    (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0))
                (=> (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0)
                    main@%_14_0)
                (=> (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0)
                    (= main@%.0._0 main@%.0..pre_0))
                (=> (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0)
                    (= main@%.0.3_0 main@%.0.3.pre_0))
                (=> (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0)
                    (= main@%.0._1 main@%.0._0))
                (=> (and main@inc_max_repeat.exit_0 main@tailrecurse.i_0)
                    (= main@%.0.3_1 main@%.0.3_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_15_0 (- main@%.0.3_1 main@%.0._1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_16_0 (> main@%_15_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_16_0))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_17_0 (- main@%.0._1 main@%.0.3_1)))
                (=> main@inc_max_repeat.exit_0
                    (= main@%_18_0 (> main@%_17_0 main@%_4_0)))
                (=> main@inc_max_repeat.exit_0 (not main@%_18_0))
                (=> main@inc_max_repeat.exit.split_0
                    (and main@inc_max_repeat.exit.split_0
                         main@inc_max_repeat.exit_0))
                main@inc_max_repeat.exit.split_0)))
  (=> a!1 main@inc_max_repeat.exit.split)))
(query main@inc_max_repeat.exit.split)

