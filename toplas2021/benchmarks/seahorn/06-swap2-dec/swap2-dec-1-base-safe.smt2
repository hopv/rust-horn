(set-info :original "06-swap2-dec/swap2-dec-1-base-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@empty.loop (Int Int Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i ((Array Int Int) (Array Int Int) Int Int Int Int Int Int ))
(declare-rel main@swap2_dec.exit.split ())
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.06_2 Int )
(declare-var main@%.0_2 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast8_0 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.06_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.06_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select9_0 Int )
(declare-var main@_17_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@_23_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@swap2_dec.exit_0 Bool )
(declare-var main@swap2_dec.exit.split_0 Bool )
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
         (> main@%_3_0 0)
         (> main@%_4_0 0)
         (= main@%_5_0 main@%_1_0)
         (= main@%_6_0 @nd_0)
         (= main@%sm_0 (store main@%sm8_0 main@%_1_0 main@%_7_0))
         (= main@%_8_0 main@%_2_0)
         (= main@%_9_0 @nd_0)
         (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_10_0))
         (= main@%.0.sroa_cast_0 main@%_3_0)
         (= main@%sm2_0 (store main@%sm9_0 main@%_3_0 main@%_1_0))
         (= main@%.0.sroa_cast8_0 main@%_4_0)
         (= main@%sm3_0 (store main@%sm2_0 main@%_4_0 main@%_2_0))
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop main@%_1_0
                     main@%_7_0
                     @nd_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%sm1_0
                     main@%_3_0
                     main@%_4_0)))
(rule (=> (and (main@empty.loop main@%_1_0
                          main@%_7_0
                          @nd_0
                          main@%loop.bound_0
                          main@%sm3_0
                          main@%sm1_0
                          main@%_3_0
                          main@%_4_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop main@%_1_0
                     main@%_7_0
                     @nd_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%sm1_0
                     main@%_3_0
                     main@%_4_0)))
(rule (=> (and (main@empty.loop main@%_1_0
                          main@%_7_0
                          @nd_0
                          main@%loop.bound_0
                          main@%sm3_0
                          main@%sm1_0
                          main@%_3_0
                          main@%_4_0)
         true
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@empty.loop_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (not main@%nd.loop.cond_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_0 main@%sm3_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_0 main@%sm1_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.06_0 main@%_3_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.06_1 main@%.06_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_1 main@%.0_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%shadow.mem.0.0_1
      main@%shadow.mem.4.0_1
      main@%.06_1
      main@%.0_1
      main@%_1_0
      main@%_7_0
      @nd_0
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%.06_0
                  main@%.0_0
                  main@%_1_0
                  main@%_7_0
                  @nd_0
                  main@%loop.bound_0)
                true
                (= main@%_11_0 @nd_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (= main@%spec.select_0 (ite main@%_13_0 main@%.06_0 main@%.0_0))
                (= main@%spec.select9_0
                   (ite main@%_13_0 main@%.0_0 main@%.06_0))
                (= main@%_14_0 @nd_0)
                (= main@%_16_0 (= main@%_15_0 0))
                (=> main@_17_0 (and main@_17_0 main@tailrecurse.i_0))
                (=> (and main@_17_0 main@tailrecurse.i_0) (not main@%_16_0))
                (=> main@_17_0
                    (= main@%_18_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select_0)))
                (=> main@_17_0
                    (= main@%_19_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select9_0)))
                (=> main@_17_0
                    (= main@%sm4_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select_0
                              main@%_19_0)))
                (=> main@_17_0
                    (= main@%sm5_0
                       (store main@%sm4_0 main@%spec.select9_0 main@%_18_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_17_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_16_0)
                (=> (and main@may_swap.exit.i_0 main@_17_0)
                    (= main@%shadow.mem.4.1_0 main@%sm5_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_17_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_20_0 @nd_0))
                (=> main@may_swap.exit.i_0
                    (= main@%_22_0 (= main@%_21_0 main@%loop.bound_0)))
                (=> main@_23_0 (and main@_23_0 main@may_swap.exit.i_0))
                (=> (and main@_23_0 main@may_swap.exit.i_0) main@%_22_0)
                (=> main@_23_0
                    (= main@%_24_0
                       (select main@%shadow.mem.4.1_2 main@%spec.select_0)))
                (=> main@_23_0
                    (= main@%_25_0 (select main@%shadow.mem.0.0_0 main@%_24_0)))
                (=> main@_23_0 (= main@%_26_0 (+ main@%_25_0 (- 1))))
                (=> main@_23_0
                    (= main@%sm6_0
                       (store main@%shadow.mem.0.0_0 main@%_24_0 main@%_26_0)))
                (=> main@_23_0
                    (= main@%_27_0
                       (select main@%shadow.mem.4.1_2 main@%spec.select9_0)))
                (=> main@_23_0 (= main@%_28_0 (select main@%sm6_0 main@%_27_0)))
                (=> main@_23_0 (= main@%_29_0 (+ main@%_28_0 (- 2))))
                (=> main@_23_0
                    (= main@%sm7_0 (store main@%sm6_0 main@%_27_0 main@%_29_0)))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_23_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.1_2))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.0.0_1 main@%sm7_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.06_1 main@%spec.select_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.0_1 main@%spec.select9_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.06_2 main@%.06_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.0_2 main@%.0_1))
                main@tailrecurse.i_1)))
  (=> a!1
      (main@tailrecurse.i
        main@%shadow.mem.0.0_2
        main@%shadow.mem.4.0_2
        main@%.06_2
        main@%.0_2
        main@%_1_0
        main@%_7_0
        @nd_0
        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%.06_0
                  main@%.0_0
                  main@%_1_0
                  main@%_7_0
                  @nd_0
                  main@%loop.bound_0)
                true
                (= main@%_11_0 @nd_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (= main@%spec.select_0 (ite main@%_13_0 main@%.06_0 main@%.0_0))
                (= main@%spec.select9_0
                   (ite main@%_13_0 main@%.0_0 main@%.06_0))
                (= main@%_14_0 @nd_0)
                (= main@%_16_0 (= main@%_15_0 0))
                (=> main@_17_0 (and main@_17_0 main@tailrecurse.i_0))
                (=> (and main@_17_0 main@tailrecurse.i_0) (not main@%_16_0))
                (=> main@_17_0
                    (= main@%_18_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select_0)))
                (=> main@_17_0
                    (= main@%_19_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select9_0)))
                (=> main@_17_0
                    (= main@%sm4_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select_0
                              main@%_19_0)))
                (=> main@_17_0
                    (= main@%sm5_0
                       (store main@%sm4_0 main@%spec.select9_0 main@%_18_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_17_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_16_0)
                (=> (and main@may_swap.exit.i_0 main@_17_0)
                    (= main@%shadow.mem.4.1_0 main@%sm5_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_17_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_20_0 @nd_0))
                (=> main@may_swap.exit.i_0
                    (= main@%_22_0 (= main@%_21_0 main@%loop.bound_0)))
                (=> main@swap2_dec.exit_0
                    (and main@swap2_dec.exit_0 main@may_swap.exit.i_0))
                (=> (and main@swap2_dec.exit_0 main@may_swap.exit.i_0)
                    (not main@%_22_0))
                (=> main@swap2_dec.exit_0
                    (= main@%_30_0 (select main@%shadow.mem.0.0_0 main@%_1_0)))
                (=> main@swap2_dec.exit_0
                    (= main@%_31_0 (< main@%_7_0 main@%_30_0)))
                (=> main@swap2_dec.exit_0 main@%_31_0)
                (=> main@swap2_dec.exit.split_0
                    (and main@swap2_dec.exit.split_0 main@swap2_dec.exit_0))
                main@swap2_dec.exit.split_0)))
  (=> a!1 main@swap2_dec.exit.split)))
(query main@swap2_dec.exit.split)

