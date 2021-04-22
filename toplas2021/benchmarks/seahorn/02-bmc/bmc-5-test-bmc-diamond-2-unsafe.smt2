(set-info :original "02-bmc/bmc-5-test-bmc-diamond-2-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@empty.loop (Int Int Int Int Int Int ))
(declare-rel main@_7 (Int Int Int Int Int Int ))
(declare-rel main@_12 (Int Int Int Int Int ))
(declare-rel main@_17 (Int Int Int Int ))
(declare-rel main@_22 (Int Int Int ))
(declare-rel main@_27 (Int Int ))
(declare-rel main@_32 (Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%loop.bound4_0 Int )
(declare-var main@%loop.bound5_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_7_0 Bool )
(declare-var main@_7_1 Bool )
(declare-var main@_10_0 Bool )
(declare-var main@_12_0 Bool )
(declare-var main@_12_1 Bool )
(declare-var main@_15_0 Bool )
(declare-var main@_17_0 Bool )
(declare-var main@_17_1 Bool )
(declare-var main@_20_0 Bool )
(declare-var main@_22_0 Bool )
(declare-var main@_22_1 Bool )
(declare-var main@_25_0 Bool )
(declare-var main@_27_0 Bool )
(declare-var main@_27_1 Bool )
(declare-var main@_30_0 Bool )
(declare-var main@_32_0 Bool )
(declare-var main@_32_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 0))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 0))
         main@%_2_0
         (= main@%_3_0 (= main@%loop.bound3_0 0))
         main@%_3_0
         (= main@%_4_0 (= main@%loop.bound4_0 0))
         main@%_4_0
         (= main@%_5_0 (= main@%loop.bound5_0 0))
         main@%_5_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%loop.bound4_0
                     main@%loop.bound5_0)))
(rule (=> (and (main@empty.loop main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%loop.bound3_0
                          main@%loop.bound4_0
                          main@%loop.bound5_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%loop.bound4_0
                     main@%loop.bound5_0)))
(rule (=> (and (main@empty.loop main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%loop.bound3_0
                          main@%loop.bound4_0
                          main@%loop.bound5_0)
         true
         (=> main@_7_0 (and main@_7_0 main@empty.loop_0))
         (=> (and main@_7_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         main@_7_0)
    (main@_7 main@%loop.bound_0
             main@%loop.bound1_0
             main@%loop.bound2_0
             main@%loop.bound3_0
             main@%loop.bound4_0
             main@%loop.bound5_0)))
(rule (=> (and (main@_7 main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0
                  main@%loop.bound3_0
                  main@%loop.bound4_0
                  main@%loop.bound5_0)
         true
         (= main@%_9_0 (= main@%_8_0 main@%loop.bound5_0))
         (=> main@_7_1 (and main@_7_1 main@_7_0))
         (=> (and main@_7_1 main@_7_0) (not main@%_9_0))
         main@_7_1)
    (main@_7 main@%loop.bound_0
             main@%loop.bound1_0
             main@%loop.bound2_0
             main@%loop.bound3_0
             main@%loop.bound4_0
             main@%loop.bound5_0)))
(rule (=> (and (main@_7 main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0
                  main@%loop.bound3_0
                  main@%loop.bound4_0
                  main@%loop.bound5_0)
         true
         (= main@%_9_0 (= main@%_8_0 main@%loop.bound5_0))
         (=> main@_10_0 (and main@_10_0 main@_7_0))
         (=> (and main@_10_0 main@_7_0) main@%_9_0)
         (=> main@_12_0 (and main@_12_0 main@_10_0))
         main@_12_0)
    (main@_12 main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0
              main@%loop.bound4_0)))
(rule (=> (and (main@_12 main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0
                   main@%loop.bound4_0)
         true
         (= main@%_14_0 (= main@%_13_0 main@%loop.bound4_0))
         (=> main@_12_1 (and main@_12_1 main@_12_0))
         (=> (and main@_12_1 main@_12_0) (not main@%_14_0))
         main@_12_1)
    (main@_12 main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0
              main@%loop.bound4_0)))
(rule (=> (and (main@_12 main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0
                   main@%loop.bound4_0)
         true
         (= main@%_14_0 (= main@%_13_0 main@%loop.bound4_0))
         (=> main@_15_0 (and main@_15_0 main@_12_0))
         (=> (and main@_15_0 main@_12_0) main@%_14_0)
         (=> main@_17_0 (and main@_17_0 main@_15_0))
         main@_17_0)
    (main@_17 main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0)))
(rule (=> (and (main@_17 main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0)
         true
         (= main@%_19_0 (= main@%_18_0 main@%loop.bound3_0))
         (=> main@_17_1 (and main@_17_1 main@_17_0))
         (=> (and main@_17_1 main@_17_0) (not main@%_19_0))
         main@_17_1)
    (main@_17 main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0)))
(rule (=> (and (main@_17 main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0)
         true
         (= main@%_19_0 (= main@%_18_0 main@%loop.bound3_0))
         (=> main@_20_0 (and main@_20_0 main@_17_0))
         (=> (and main@_20_0 main@_17_0) main@%_19_0)
         (=> main@_22_0 (and main@_22_0 main@_20_0))
         main@_22_0)
    (main@_22 main@%loop.bound_0 main@%loop.bound1_0 main@%loop.bound2_0)))
(rule (=> (and (main@_22 main@%loop.bound_0 main@%loop.bound1_0 main@%loop.bound2_0)
         true
         (= main@%_24_0 (= main@%_23_0 main@%loop.bound2_0))
         (=> main@_22_1 (and main@_22_1 main@_22_0))
         (=> (and main@_22_1 main@_22_0) (not main@%_24_0))
         main@_22_1)
    (main@_22 main@%loop.bound_0 main@%loop.bound1_0 main@%loop.bound2_0)))
(rule (=> (and (main@_22 main@%loop.bound_0 main@%loop.bound1_0 main@%loop.bound2_0)
         true
         (= main@%_24_0 (= main@%_23_0 main@%loop.bound2_0))
         (=> main@_25_0 (and main@_25_0 main@_22_0))
         (=> (and main@_25_0 main@_22_0) main@%_24_0)
         (=> main@_27_0 (and main@_27_0 main@_25_0))
         main@_27_0)
    (main@_27 main@%loop.bound_0 main@%loop.bound1_0)))
(rule (=> (and (main@_27 main@%loop.bound_0 main@%loop.bound1_0)
         true
         (= main@%_29_0 (= main@%_28_0 main@%loop.bound1_0))
         (=> main@_27_1 (and main@_27_1 main@_27_0))
         (=> (and main@_27_1 main@_27_0) (not main@%_29_0))
         main@_27_1)
    (main@_27 main@%loop.bound_0 main@%loop.bound1_0)))
(rule (=> (and (main@_27 main@%loop.bound_0 main@%loop.bound1_0)
         true
         (= main@%_29_0 (= main@%_28_0 main@%loop.bound1_0))
         (=> main@_30_0 (and main@_30_0 main@_27_0))
         (=> (and main@_30_0 main@_27_0) main@%_29_0)
         (=> main@_32_0 (and main@_32_0 main@_30_0))
         main@_32_0)
    (main@_32 main@%loop.bound_0)))
(rule (=> (and (main@_32 main@%loop.bound_0)
         true
         (= main@%_34_0 (= main@%_33_0 main@%loop.bound_0))
         (=> main@_32_1 (and main@_32_1 main@_32_0))
         (=> (and main@_32_1 main@_32_0) (not main@%_34_0))
         main@_32_1)
    (main@_32 main@%loop.bound_0)))
(rule (=> (and (main@_32 main@%loop.bound_0)
         true
         (= main@%_34_0 (= main@%_33_0 main@%loop.bound_0))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@_32_0))
         (=> (and main@verifier.error_0 main@_32_0) main@%_34_0)
         true
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(query main@verifier.error.split)

