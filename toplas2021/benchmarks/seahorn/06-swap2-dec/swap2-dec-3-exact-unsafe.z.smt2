(set-info :original "06-swap2-dec/swap2-dec-3-exact-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@empty.loop (Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Bool )
(declare-var main@%_32_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.07_2 Int )
(declare-var main@%.0_2 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast9_0 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%.07_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%.tr.i_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%.07_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%.tr.i_1 Int )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select10_0 Int )
(declare-var main@_19_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@_23_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_30_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%.tr.i_2 Int )
(declare-var main@swap2_dec_bound.exit_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@_33_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
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
         (distinct main@%_1_0 main@%_2_0 main@%_3_0 main@%_4_0) ; added
         (= main@%_5_0 @nd_0)
         (= main@%_7_0 main@%_1_0)
         (= main@%_8_0 @nd_0)
         (= main@%sm_0 (store main@%sm9_0 main@%_1_0 main@%_9_0))
         (= main@%_10_0 main@%_2_0)
         (= main@%_11_0 @nd_0)
         (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_12_0))
         (= main@%.0.sroa_cast_0 main@%_3_0)
         (= main@%sm2_0 (store main@%sm8_0 main@%_3_0 main@%_1_0))
         (= main@%.0.sroa_cast9_0 main@%_4_0)
         (= main@%sm3_0 (store main@%sm2_0 main@%_4_0 main@%_2_0))
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop main@%_9_0
                     main@%_6_0
                     main@%_1_0
                     main@%loop.bound_0
                     @nd_0
                     main@%sm1_0
                     main@%sm3_0
                     main@%_3_0
                     main@%_4_0)))
(rule (let ((a!1 (main@empty.loop main@%_9_0
                            main@%_6_0
                            main@%_1_0
                            main@%loop.bound_0
                            @nd_0
                            main@%sm1_0
                            main@%sm3_0
                            main@%_3_0
                            main@%_4_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop main@%_9_0
                          main@%_6_0
                          main@%_1_0
                          main@%loop.bound_0
                          @nd_0
                          main@%sm1_0
                          main@%sm3_0
                          main@%_3_0
                          main@%_4_0)
         true
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@empty.loop_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (not main@%nd.loop.cond_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_0 main@%sm1_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_0 main@%sm3_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.07_0 main@%_3_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr.i_0 main@%_6_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.07_1 main@%.07_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_1 main@%.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr.i_1 main@%.tr.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%_9_0
      main@%_6_0
      main@%shadow.mem.0.0_1
      main@%_1_0
      main@%.tr.i_1
      main@%shadow.mem.4.0_1
      main@%.07_1
      main@%.0_1
      main@%loop.bound_0
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_9_0
                  main@%_6_0
                  main@%shadow.mem.0.0_0
                  main@%_1_0
                  main@%.tr.i_0
                  main@%shadow.mem.4.0_0
                  main@%.07_0
                  main@%.0_0
                  main@%loop.bound_0
                  @nd_0)
                true
                (= main@%_13_0 @nd_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (= main@%spec.select_0 (ite main@%_15_0 main@%.07_0 main@%.0_0))
                (= main@%spec.select10_0
                   (ite main@%_15_0 main@%.0_0 main@%.07_0))
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (=> main@_19_0 (and main@_19_0 main@tailrecurse.i_0))
                (=> (and main@_19_0 main@tailrecurse.i_0) (not main@%_18_0))
                (=> main@_19_0
                    (= main@%_20_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select_0)))
                (=> main@_19_0
                    (= main@%_21_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select10_0)))
                (=> main@_19_0
                    (= main@%sm4_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select_0
                              main@%_21_0)))
                (=> main@_19_0
                    (= main@%sm5_0
                       (store main@%sm4_0 main@%spec.select10_0 main@%_20_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_19_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_18_0)
                (=> (and main@may_swap.exit.i_0 main@_19_0)
                    (= main@%shadow.mem.4.1_0 main@%sm5_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_19_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0
                    (= main@%_22_0 (= main@%.tr.i_0 main@%loop.bound_0)))
                (=> main@_23_0 (and main@_23_0 main@may_swap.exit.i_0))
                (=> (and main@_23_0 main@may_swap.exit.i_0) (not main@%_22_0))
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
                       (select main@%shadow.mem.4.1_2 main@%spec.select10_0)))
                (=> main@_23_0 (= main@%_28_0 (select main@%sm6_0 main@%_27_0)))
                (=> main@_23_0 (= main@%_29_0 (+ main@%_28_0 (- 2))))
                (=> main@_23_0
                    (= main@%sm7_0 (store main@%sm6_0 main@%_27_0 main@%_29_0)))
                (=> main@_23_0 (= main@%_30_0 (+ main@%.tr.i_0 (- 1))))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_23_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.0.0_1 main@%sm7_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.1_2))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.07_1 main@%spec.select_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.0_1 main@%spec.select10_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.tr.i_1 main@%_30_0))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.07_2 main@%.07_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.0_2 main@%.0_1))
                (=> (and main@tailrecurse.i_1 main@_23_0)
                    (= main@%.tr.i_2 main@%.tr.i_1))
                main@tailrecurse.i_1)))
  (=> a!1
      (main@tailrecurse.i
        main@%_9_0
        main@%_6_0
        main@%shadow.mem.0.0_2
        main@%_1_0
        main@%.tr.i_2
        main@%shadow.mem.4.0_2
        main@%.07_2
        main@%.0_2
        main@%loop.bound_0
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_9_0
                  main@%_6_0
                  main@%shadow.mem.0.0_0
                  main@%_1_0
                  main@%.tr.i_0
                  main@%shadow.mem.4.0_0
                  main@%.07_0
                  main@%.0_0
                  main@%loop.bound_0
                  @nd_0)
                true
                (= main@%_13_0 @nd_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (= main@%spec.select_0 (ite main@%_15_0 main@%.07_0 main@%.0_0))
                (= main@%spec.select10_0
                   (ite main@%_15_0 main@%.0_0 main@%.07_0))
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (=> main@_19_0 (and main@_19_0 main@tailrecurse.i_0))
                (=> (and main@_19_0 main@tailrecurse.i_0) (not main@%_18_0))
                (=> main@_19_0
                    (= main@%_20_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select_0)))
                (=> main@_19_0
                    (= main@%_21_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select10_0)))
                (=> main@_19_0
                    (= main@%sm4_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select_0
                              main@%_21_0)))
                (=> main@_19_0
                    (= main@%sm5_0
                       (store main@%sm4_0 main@%spec.select10_0 main@%_20_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_19_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_18_0)
                (=> (and main@may_swap.exit.i_0 main@_19_0)
                    (= main@%shadow.mem.4.1_0 main@%sm5_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_19_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0
                    (= main@%_22_0 (= main@%.tr.i_0 main@%loop.bound_0)))
                (=> main@swap2_dec_bound.exit_0
                    (and main@swap2_dec_bound.exit_0 main@may_swap.exit.i_0))
                (=> (and main@swap2_dec_bound.exit_0 main@may_swap.exit.i_0)
                    main@%_22_0)
                (=> main@swap2_dec_bound.exit_0
                    (= main@%_31_0 (select main@%shadow.mem.0.0_0 main@%_1_0)))
                (=> main@swap2_dec_bound.exit_0
                    (= main@%_32_0 (< main@%_9_0 main@%_31_0)))
                (=> main@_33_0 (and main@_33_0 main@swap2_dec_bound.exit_0))
                (=> (and main@_33_0 main@swap2_dec_bound.exit_0)
                    (not main@%_32_0))
                (=> main@_33_0 (= main@%_34_0 (- main@%_9_0 main@%_31_0)))
                (=> main@_33_0 (= main@%_35_0 (* main@%_6_0 2)))
                (=> main@_33_0 (= main@%_36_0 (< main@%_34_0 main@%_35_0)))
                (=> main@_33_0 (not main@%_36_0))
                (=> |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|
                    main@swap2_dec_bound.exit_0)
                (=> main@verifier.error_0
                    (or |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|
                        (and main@verifier.error_0 main@_33_0)))
                (=> |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|
                    main@%_32_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

