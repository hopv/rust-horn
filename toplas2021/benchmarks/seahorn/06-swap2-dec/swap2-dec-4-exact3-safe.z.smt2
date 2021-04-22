(set-info :original "06-swap2-dec/swap2-dec-4-exact3-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@empty.loop (Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_60_0 Int )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Bool )
(declare-var main@%_58_0 Bool )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%_49_0 Int )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%_50_0 Int )
(declare-var main@%_51_0 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%_45_0 Bool )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%_41_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select24_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%.2_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.019_2 Int )
(declare-var main@%.017_2 Int )
(declare-var main@%.0_2 Int )
(declare-var main@%sm15_0 (Array Int Int) )
(declare-var main@%sm16_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast22_0 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast23_0 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%.019_0 Int )
(declare-var main@%.017_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%.tr.i_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%.019_1 Int )
(declare-var main@%.017_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%.tr.i_1 Int )
(declare-var main@%.1_0 Int )
(declare-var main@%spec.select25_0 Int )
(declare-var main@%spec.select26_0 Int )
(declare-var main@_30_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@_36_0 Bool )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@may_swap.exit3.i_0 Bool )
(declare-var |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)| Bool )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@_42_0 Bool )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@may_swap.exit4.i_0 Bool )
(declare-var |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)| Bool )
(declare-var main@%shadow.mem.4.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_2 (Array Int Int) )
(declare-var main@_46_0 Bool )
(declare-var main@%sm14_0 (Array Int Int) )
(declare-var main@%_56_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%.tr.i_2 Int )
(declare-var main@swap2_dec_bound_three.exit_0 Bool )
(declare-var main@%_57_0 Int )
(declare-var main@_59_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)| Bool )
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
         (> main@%_5_0 0)
         (> main@%_6_0 0)
         (distinct main@%_1_0 main@%_2_0 main@%_3_0
            main@%_4_0 main@%_5_0 main@%_6_0) ; added
         (= main@%_7_0 @nd_0)
         (= main@%_9_0 main@%_1_0)
         (= main@%_10_0 @nd_0)
         (= main@%sm_0 (store main@%sm16_0 main@%_1_0 main@%_11_0))
         (= main@%_12_0 main@%_2_0)
         (= main@%_13_0 @nd_0)
         (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_14_0))
         (= main@%_15_0 main@%_3_0)
         (= main@%_16_0 @nd_0)
         (= main@%sm2_0 (store main@%sm1_0 main@%_3_0 main@%_17_0))
         (= main@%.0.sroa_cast_0 main@%_4_0)
         (= main@%sm3_0 (store main@%sm15_0 main@%_4_0 main@%_1_0))
         (= main@%.0.sroa_cast22_0 main@%_5_0)
         (= main@%sm4_0 (store main@%sm3_0 main@%_5_0 main@%_2_0))
         (= main@%.0.sroa_cast23_0 main@%_6_0)
         (= main@%sm5_0 (store main@%sm4_0 main@%_6_0 main@%_3_0))
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop main@%_11_0
                     main@%_8_0
                     main@%_1_0
                     main@%loop.bound_0
                     @nd_0
                     main@%sm2_0
                     main@%sm5_0
                     main@%_4_0
                     main@%_5_0
                     main@%_6_0)))
(rule (let ((a!1 (main@empty.loop main@%_11_0
                            main@%_8_0
                            main@%_1_0
                            main@%loop.bound_0
                            @nd_0
                            main@%sm2_0
                            main@%sm5_0
                            main@%_4_0
                            main@%_5_0
                            main@%_6_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop main@%_11_0
                          main@%_8_0
                          main@%_1_0
                          main@%loop.bound_0
                          @nd_0
                          main@%sm2_0
                          main@%sm5_0
                          main@%_4_0
                          main@%_5_0
                          main@%_6_0)
         true
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@empty.loop_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (not main@%nd.loop.cond_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_0 main@%sm2_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_0 main@%sm5_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.019_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.017_0 main@%_5_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_0 main@%_6_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr.i_0 main@%_8_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.019_1 main@%.019_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.017_1 main@%.017_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.0_1 main@%.0_0))
         (=> (and main@tailrecurse.i_0 main@empty.loop_0)
             (= main@%.tr.i_1 main@%.tr.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%_11_0
      main@%_8_0
      main@%shadow.mem.0.0_1
      main@%_1_0
      main@%.tr.i_1
      main@%shadow.mem.4.0_1
      main@%.019_1
      main@%.017_1
      main@%.0_1
      main@%loop.bound_0
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_11_0
                  main@%_8_0
                  main@%shadow.mem.0.0_0
                  main@%_1_0
                  main@%.tr.i_0
                  main@%shadow.mem.4.0_0
                  main@%.019_0
                  main@%.017_0
                  main@%.0_0
                  main@%loop.bound_0
                  @nd_0)
                true
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%spec.select_0
                   (ite main@%_20_0 main@%.019_0 main@%.017_0))
                (= main@%spec.select24_0
                   (ite main@%_20_0 main@%.017_0 main@%.019_0))
                (= main@%_21_0 @nd_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (= main@%.2_0
                   (ite main@%_23_0 main@%spec.select24_0 main@%.0_0))
                (= main@%.1_0
                   (ite main@%_23_0 main@%.0_0 main@%spec.select24_0))
                (= main@%_24_0 @nd_0)
                (= main@%_26_0 (= main@%_25_0 0))
                (= main@%spec.select25_0
                   (ite main@%_26_0 main@%spec.select_0 main@%.2_0))
                (= main@%spec.select26_0
                   (ite main@%_26_0 main@%.2_0 main@%spec.select_0))
                (= main@%_27_0 @nd_0)
                (= main@%_29_0 (= main@%_28_0 0))
                (=> main@_30_0 (and main@_30_0 main@tailrecurse.i_0))
                (=> (and main@_30_0 main@tailrecurse.i_0) (not main@%_29_0))
                (=> main@_30_0
                    (= main@%_31_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select25_0)))
                (=> main@_30_0
                    (= main@%_32_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select26_0)))
                (=> main@_30_0
                    (= main@%sm6_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select25_0
                              main@%_32_0)))
                (=> main@_30_0
                    (= main@%sm7_0
                       (store main@%sm6_0 main@%spec.select26_0 main@%_31_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_30_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_29_0)
                (=> (and main@may_swap.exit.i_0 main@_30_0)
                    (= main@%shadow.mem.4.1_0 main@%sm7_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_30_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_33_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_35_0 (= main@%_34_0 0)))
                (=> main@_36_0 (and main@_36_0 main@may_swap.exit.i_0))
                (=> (and main@_36_0 main@may_swap.exit.i_0) (not main@%_35_0))
                (=> main@_36_0
                    (= main@%_37_0
                       (select main@%shadow.mem.4.1_2 main@%spec.select26_0)))
                (=> main@_36_0
                    (= main@%_38_0 (select main@%shadow.mem.4.1_2 main@%.1_0)))
                (=> main@_36_0
                    (= main@%sm8_0
                       (store main@%shadow.mem.4.1_2
                              main@%spec.select26_0
                              main@%_38_0)))
                (=> main@_36_0
                    (= main@%sm9_0 (store main@%sm8_0 main@%.1_0 main@%_37_0)))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@may_swap.exit.i_0)
                (=> main@may_swap.exit3.i_0
                    (or (and main@may_swap.exit3.i_0 main@_36_0)
                        |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@%_35_0)
                (=> (and main@may_swap.exit3.i_0 main@_36_0)
                    (= main@%shadow.mem.4.2_0 main@%sm9_0))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_2))
                (=> (and main@may_swap.exit3.i_0 main@_36_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@may_swap.exit3.i_0 (= main@%_39_0 @nd_0))
                (=> main@may_swap.exit3.i_0 (= main@%_41_0 (= main@%_40_0 0)))
                (=> main@_42_0 (and main@_42_0 main@may_swap.exit3.i_0))
                (=> (and main@_42_0 main@may_swap.exit3.i_0) (not main@%_41_0))
                (=> main@_42_0
                    (= main@%_43_0
                       (select main@%shadow.mem.4.2_2 main@%spec.select25_0)))
                (=> main@_42_0
                    (= main@%_44_0
                       (select main@%shadow.mem.4.2_2 main@%spec.select26_0)))
                (=> main@_42_0
                    (= main@%sm10_0
                       (store main@%shadow.mem.4.2_2
                              main@%spec.select25_0
                              main@%_44_0)))
                (=> main@_42_0
                    (= main@%sm11_0
                       (store main@%sm10_0 main@%spec.select26_0 main@%_43_0)))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@may_swap.exit3.i_0)
                (=> main@may_swap.exit4.i_0
                    (or (and main@may_swap.exit4.i_0 main@_42_0)
                        |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@%_41_0)
                (=> (and main@may_swap.exit4.i_0 main@_42_0)
                    (= main@%shadow.mem.4.3_0 main@%sm11_0))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_2))
                (=> (and main@may_swap.exit4.i_0 main@_42_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@may_swap.exit4.i_0
                    (= main@%_45_0 (= main@%.tr.i_0 main@%loop.bound_0)))
                (=> main@_46_0 (and main@_46_0 main@may_swap.exit4.i_0))
                (=> (and main@_46_0 main@may_swap.exit4.i_0) (not main@%_45_0))
                (=> main@_46_0
                    (= main@%_47_0
                       (select main@%shadow.mem.4.3_2 main@%spec.select25_0)))
                (=> main@_46_0
                    (= main@%_48_0 (select main@%shadow.mem.0.0_0 main@%_47_0)))
                (=> main@_46_0 (= main@%_49_0 (+ main@%_48_0 (- 1))))
                (=> main@_46_0
                    (= main@%sm12_0
                       (store main@%shadow.mem.0.0_0 main@%_47_0 main@%_49_0)))
                (=> main@_46_0
                    (= main@%_50_0
                       (select main@%shadow.mem.4.3_2 main@%spec.select26_0)))
                (=> main@_46_0
                    (= main@%_51_0 (select main@%sm12_0 main@%_50_0)))
                (=> main@_46_0 (= main@%_52_0 (+ main@%_51_0 (- 2))))
                (=> main@_46_0
                    (= main@%sm13_0
                       (store main@%sm12_0 main@%_50_0 main@%_52_0)))
                (=> main@_46_0
                    (= main@%_53_0 (select main@%shadow.mem.4.3_2 main@%.1_0)))
                (=> main@_46_0
                    (= main@%_54_0 (select main@%sm13_0 main@%_53_0)))
                (=> main@_46_0 (= main@%_55_0 (+ main@%_54_0 (- 3))))
                (=> main@_46_0
                    (= main@%sm14_0
                       (store main@%sm13_0 main@%_53_0 main@%_55_0)))
                (=> main@_46_0 (= main@%_56_0 (+ main@%.tr.i_0 (- 1))))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_46_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%shadow.mem.0.0_1 main@%sm14_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.3_2))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.019_1 main@%spec.select25_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.017_1 main@%spec.select26_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.0_1 main@%.1_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.tr.i_1 main@%_56_0))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.019_2 main@%.019_1))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.017_2 main@%.017_1))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.0_2 main@%.0_1))
                (=> (and main@tailrecurse.i_1 main@_46_0)
                    (= main@%.tr.i_2 main@%.tr.i_1))
                main@tailrecurse.i_1)))
  (=> a!1
      (main@tailrecurse.i
        main@%_11_0
        main@%_8_0
        main@%shadow.mem.0.0_2
        main@%_1_0
        main@%.tr.i_2
        main@%shadow.mem.4.0_2
        main@%.019_2
        main@%.017_2
        main@%.0_2
        main@%loop.bound_0
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_11_0
                  main@%_8_0
                  main@%shadow.mem.0.0_0
                  main@%_1_0
                  main@%.tr.i_0
                  main@%shadow.mem.4.0_0
                  main@%.019_0
                  main@%.017_0
                  main@%.0_0
                  main@%loop.bound_0
                  @nd_0)
                true
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%spec.select_0
                   (ite main@%_20_0 main@%.019_0 main@%.017_0))
                (= main@%spec.select24_0
                   (ite main@%_20_0 main@%.017_0 main@%.019_0))
                (= main@%_21_0 @nd_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (= main@%.2_0
                   (ite main@%_23_0 main@%spec.select24_0 main@%.0_0))
                (= main@%.1_0
                   (ite main@%_23_0 main@%.0_0 main@%spec.select24_0))
                (= main@%_24_0 @nd_0)
                (= main@%_26_0 (= main@%_25_0 0))
                (= main@%spec.select25_0
                   (ite main@%_26_0 main@%spec.select_0 main@%.2_0))
                (= main@%spec.select26_0
                   (ite main@%_26_0 main@%.2_0 main@%spec.select_0))
                (= main@%_27_0 @nd_0)
                (= main@%_29_0 (= main@%_28_0 0))
                (=> main@_30_0 (and main@_30_0 main@tailrecurse.i_0))
                (=> (and main@_30_0 main@tailrecurse.i_0) (not main@%_29_0))
                (=> main@_30_0
                    (= main@%_31_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select25_0)))
                (=> main@_30_0
                    (= main@%_32_0
                       (select main@%shadow.mem.4.0_0 main@%spec.select26_0)))
                (=> main@_30_0
                    (= main@%sm6_0
                       (store main@%shadow.mem.4.0_0
                              main@%spec.select25_0
                              main@%_32_0)))
                (=> main@_30_0
                    (= main@%sm7_0
                       (store main@%sm6_0 main@%spec.select26_0 main@%_31_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_30_0)
                        |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@%_29_0)
                (=> (and main@may_swap.exit.i_0 main@_30_0)
                    (= main@%shadow.mem.4.1_0 main@%sm7_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.0_0))
                (=> (and main@may_swap.exit.i_0 main@_30_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_33_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_35_0 (= main@%_34_0 0)))
                (=> main@_36_0 (and main@_36_0 main@may_swap.exit.i_0))
                (=> (and main@_36_0 main@may_swap.exit.i_0) (not main@%_35_0))
                (=> main@_36_0
                    (= main@%_37_0
                       (select main@%shadow.mem.4.1_2 main@%spec.select26_0)))
                (=> main@_36_0
                    (= main@%_38_0 (select main@%shadow.mem.4.1_2 main@%.1_0)))
                (=> main@_36_0
                    (= main@%sm8_0
                       (store main@%shadow.mem.4.1_2
                              main@%spec.select26_0
                              main@%_38_0)))
                (=> main@_36_0
                    (= main@%sm9_0 (store main@%sm8_0 main@%.1_0 main@%_37_0)))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@may_swap.exit.i_0)
                (=> main@may_swap.exit3.i_0
                    (or (and main@may_swap.exit3.i_0 main@_36_0)
                        |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@%_35_0)
                (=> (and main@may_swap.exit3.i_0 main@_36_0)
                    (= main@%shadow.mem.4.2_0 main@%sm9_0))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_2))
                (=> (and main@may_swap.exit3.i_0 main@_36_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@may_swap.exit3.i_0 (= main@%_39_0 @nd_0))
                (=> main@may_swap.exit3.i_0 (= main@%_41_0 (= main@%_40_0 0)))
                (=> main@_42_0 (and main@_42_0 main@may_swap.exit3.i_0))
                (=> (and main@_42_0 main@may_swap.exit3.i_0) (not main@%_41_0))
                (=> main@_42_0
                    (= main@%_43_0
                       (select main@%shadow.mem.4.2_2 main@%spec.select25_0)))
                (=> main@_42_0
                    (= main@%_44_0
                       (select main@%shadow.mem.4.2_2 main@%spec.select26_0)))
                (=> main@_42_0
                    (= main@%sm10_0
                       (store main@%shadow.mem.4.2_2
                              main@%spec.select25_0
                              main@%_44_0)))
                (=> main@_42_0
                    (= main@%sm11_0
                       (store main@%sm10_0 main@%spec.select26_0 main@%_43_0)))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@may_swap.exit3.i_0)
                (=> main@may_swap.exit4.i_0
                    (or (and main@may_swap.exit4.i_0 main@_42_0)
                        |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@%_41_0)
                (=> (and main@may_swap.exit4.i_0 main@_42_0)
                    (= main@%shadow.mem.4.3_0 main@%sm11_0))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_2))
                (=> (and main@may_swap.exit4.i_0 main@_42_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@may_swap.exit4.i_0
                    (= main@%_45_0 (= main@%.tr.i_0 main@%loop.bound_0)))
                (=> main@swap2_dec_bound_three.exit_0
                    (and main@swap2_dec_bound_three.exit_0
                         main@may_swap.exit4.i_0))
                (=> (and main@swap2_dec_bound_three.exit_0
                         main@may_swap.exit4.i_0)
                    main@%_45_0)
                (=> main@swap2_dec_bound_three.exit_0
                    (= main@%_57_0 (select main@%shadow.mem.0.0_0 main@%_1_0)))
                (=> main@swap2_dec_bound_three.exit_0
                    (= main@%_58_0 (< main@%_11_0 main@%_57_0)))
                (=> main@_59_0
                    (and main@_59_0 main@swap2_dec_bound_three.exit_0))
                (=> (and main@_59_0 main@swap2_dec_bound_three.exit_0)
                    (not main@%_58_0))
                (=> main@_59_0 (= main@%_60_0 (- main@%_11_0 main@%_57_0)))
                (=> main@_59_0 (= main@%_61_0 (* main@%_8_0 3)))
                (=> main@_59_0 (= main@%_62_0 (> main@%_60_0 main@%_61_0)))
                (=> main@_59_0 main@%_62_0)
                (=> |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|
                    main@swap2_dec_bound_three.exit_0)
                (=> main@verifier.error_0
                    (or |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|
                        (and main@verifier.error_0 main@_59_0)))
                (=> |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|
                    main@%_58_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

