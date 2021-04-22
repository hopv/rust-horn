(set-info :original "04-inc-max/inc-max-4-repeat3-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int Int Int Int ))
(declare-rel main@inc_max_three_repeat.exit.split ())
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var @nd_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%.tr1.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%.tr1.i_0 Int )
(declare-var main@%.tr1.i_1 Int )
(declare-var main@inc_max_three_repeat.exit_0 Bool )
(declare-var main@inc_max_three_repeat.exit.split_0 Bool )
(declare-var main@%_10_0 Int )
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
         (= main@%_1_0 @nd_0)
         (= main@%_3_0 @nd_0)
         (= main@%_5_0 @nd_0)
         (= main@%_7_0 @nd_0)
         (= main@%_9_0 (= main@%_2_0 0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (not main@%_9_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr1.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr1.i_1 main@%.tr1.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%_4_0
      main@%_6_0
      main@%_2_0
      main@%.tr1.i_1
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (= main@%_1_0 @nd_0)
                (= main@%_3_0 @nd_0)
                (= main@%_5_0 @nd_0)
                (= main@%_7_0 @nd_0)
                (= main@%_9_0 (= main@%_2_0 0))
                (=> main@inc_max_three_repeat.exit_0
                    (and main@inc_max_three_repeat.exit_0 main@entry_0))
                (=> (and main@inc_max_three_repeat.exit_0 main@entry_0)
                    main@%_9_0)
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_12_0 (- main@%_4_0 main@%_6_0)))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_13_0 (> main@%_12_0 main@%_2_0)))
                (=> main@inc_max_three_repeat.exit_0 (not main@%_13_0))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_14_0 (- main@%_6_0 main@%_4_0)))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_15_0 (> main@%_14_0 main@%_2_0)))
                (=> main@inc_max_three_repeat.exit_0 (not main@%_15_0))
                (=> main@inc_max_three_repeat.exit.split_0
                    (and main@inc_max_three_repeat.exit.split_0
                         main@inc_max_three_repeat.exit_0))
                main@inc_max_three_repeat.exit.split_0)))
  (=> a!1 main@inc_max_three_repeat.exit.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_4_0
           main@%_6_0
           main@%_2_0
           main@%.tr1.i_0
           main@%loop.bound_0)
         true
         (= main@%_10_0 (+ main@%.tr1.i_0 (- 1)))
         (= main@%_11_0 (= main@%_10_0 main@%loop.bound_0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_11_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr1.i_1 main@%_10_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr1.i_2 main@%.tr1.i_1))
         main@tailrecurse.i_1)
    (main@tailrecurse.i
      main@%_4_0
      main@%_6_0
      main@%_2_0
      main@%.tr1.i_2
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%_6_0
                  main@%_2_0
                  main@%.tr1.i_0
                  main@%loop.bound_0)
                true
                (= main@%_10_0 (+ main@%.tr1.i_0 (- 1)))
                (= main@%_11_0 (= main@%_10_0 main@%loop.bound_0))
                (=> main@inc_max_three_repeat.exit_0
                    (and main@inc_max_three_repeat.exit_0 main@tailrecurse.i_0))
                (=> (and main@inc_max_three_repeat.exit_0 main@tailrecurse.i_0)
                    main@%_11_0)
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_12_0 (- main@%_4_0 main@%_6_0)))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_13_0 (> main@%_12_0 main@%_2_0)))
                (=> main@inc_max_three_repeat.exit_0 (not main@%_13_0))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_14_0 (- main@%_6_0 main@%_4_0)))
                (=> main@inc_max_three_repeat.exit_0
                    (= main@%_15_0 (> main@%_14_0 main@%_2_0)))
                (=> main@inc_max_three_repeat.exit_0 (not main@%_15_0))
                (=> main@inc_max_three_repeat.exit.split_0
                    (and main@inc_max_three_repeat.exit.split_0
                         main@inc_max_three_repeat.exit_0))
                main@inc_max_three_repeat.exit.split_0)))
  (=> a!1 main@inc_max_three_repeat.exit.split)))
(query main@inc_max_three_repeat.exit.split)

