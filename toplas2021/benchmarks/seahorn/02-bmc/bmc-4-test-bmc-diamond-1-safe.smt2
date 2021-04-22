(set-info :original "02-bmc/bmc-4-test-bmc-diamond-1-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@empty.loop (Int Int Int Int Int Int ))
(declare-rel main@_11 (Int Int Int Int Int Int ))
(declare-rel main@_16 (Int Int Int Int Int ))
(declare-rel main@_21 (Int Int Int Int ))
(declare-rel main@.preheader1 (Int Int Int ))
(declare-rel main@.preheader (Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_28_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%_6_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%loop.bound4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_11_0 Bool )
(declare-var main@_11_1 Bool )
(declare-var main@_14_0 Bool )
(declare-var main@_16_0 Bool )
(declare-var main@_16_1 Bool )
(declare-var main@_19_0 Bool )
(declare-var main@_21_0 Bool )
(declare-var main@_21_1 Bool )
(declare-var main@.preheader1_0 Bool )
(declare-var main@.preheader1_1 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@.preheader_1 Bool )
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
         (= main@%_6_0 (> main@%_5_0 0))
         main@%_6_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop main@%_5_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%loop.bound4_0)))
(rule (=> (and (main@empty.loop main@%_5_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%loop.bound3_0
                          main@%loop.bound4_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop main@%_5_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%loop.bound4_0)))
(rule (=> (and (main@empty.loop main@%_5_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%loop.bound3_0
                          main@%loop.bound4_0)
         true
         (=> main@_11_0 (and main@_11_0 main@empty.loop_0))
         (=> (and main@_11_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         main@_11_0)
    (main@_11 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0
              main@%loop.bound4_0)))
(rule (=> (and (main@_11 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0
                   main@%loop.bound4_0)
         true
         (= main@%_13_0 (= main@%_12_0 main@%loop.bound4_0))
         (=> main@_11_1 (and main@_11_1 main@_11_0))
         (=> (and main@_11_1 main@_11_0) (not main@%_13_0))
         main@_11_1)
    (main@_11 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0
              main@%loop.bound4_0)))
(rule (=> (and (main@_11 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0
                   main@%loop.bound4_0)
         true
         (= main@%_13_0 (= main@%_12_0 main@%loop.bound4_0))
         (=> main@_14_0 (and main@_14_0 main@_11_0))
         (=> (and main@_14_0 main@_11_0) main@%_13_0)
         (=> main@_16_0 (and main@_16_0 main@_14_0))
         main@_16_0)
    (main@_16 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0)))
(rule (=> (and (main@_16 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0)
         true
         (= main@%_18_0 (= main@%_17_0 main@%loop.bound3_0))
         (=> main@_16_1 (and main@_16_1 main@_16_0))
         (=> (and main@_16_1 main@_16_0) (not main@%_18_0))
         main@_16_1)
    (main@_16 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0
              main@%loop.bound3_0)))
(rule (=> (and (main@_16 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0
                   main@%loop.bound3_0)
         true
         (= main@%_18_0 (= main@%_17_0 main@%loop.bound3_0))
         (=> main@_19_0 (and main@_19_0 main@_16_0))
         (=> (and main@_19_0 main@_16_0) main@%_18_0)
         (=> main@_21_0 (and main@_21_0 main@_19_0))
         main@_21_0)
    (main@_21 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0)))
(rule (=> (and (main@_21 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0)
         true
         (= main@%_23_0 (= main@%_22_0 main@%loop.bound2_0))
         (=> main@_21_1 (and main@_21_1 main@_21_0))
         (=> (and main@_21_1 main@_21_0) (not main@%_23_0))
         main@_21_1)
    (main@_21 main@%_5_0
              main@%loop.bound_0
              main@%loop.bound1_0
              main@%loop.bound2_0)))
(rule (=> (and (main@_21 main@%_5_0
                   main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0)
         true
         (= main@%_23_0 (= main@%_22_0 main@%loop.bound2_0))
         (=> main@.preheader1_0 (and main@.preheader1_0 main@_21_0))
         (=> (and main@.preheader1_0 main@_21_0) main@%_23_0)
         main@.preheader1_0)
    (main@.preheader1 main@%_5_0 main@%loop.bound_0 main@%loop.bound1_0)))
(rule (=> (and (main@.preheader1 main@%_5_0 main@%loop.bound_0 main@%loop.bound1_0)
         true
         (= main@%_25_0 (= main@%_24_0 main@%loop.bound1_0))
         (=> main@.preheader1_1 (and main@.preheader1_1 main@.preheader1_0))
         (=> (and main@.preheader1_1 main@.preheader1_0) (not main@%_25_0))
         main@.preheader1_1)
    (main@.preheader1 main@%_5_0 main@%loop.bound_0 main@%loop.bound1_0)))
(rule (=> (and (main@.preheader1 main@%_5_0 main@%loop.bound_0 main@%loop.bound1_0)
         true
         (= main@%_25_0 (= main@%_24_0 main@%loop.bound1_0))
         (=> main@.preheader_0 (and main@.preheader_0 main@.preheader1_0))
         (=> (and main@.preheader_0 main@.preheader1_0) main@%_25_0)
         main@.preheader_0)
    (main@.preheader main@%_5_0 main@%loop.bound_0)))
(rule (=> (and (main@.preheader main@%_5_0 main@%loop.bound_0)
         true
         (= main@%_27_0 (= main@%_26_0 main@%loop.bound_0))
         (=> main@.preheader_1 (and main@.preheader_1 main@.preheader_0))
         (=> (and main@.preheader_1 main@.preheader_0) (not main@%_27_0))
         main@.preheader_1)
    (main@.preheader main@%_5_0 main@%loop.bound_0)))
(rule (let ((a!1 (and (main@.preheader main@%_5_0 main@%loop.bound_0)
                true
                (= main@%_27_0 (= main@%_26_0 main@%loop.bound_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0) main@%_27_0)
                (=> main@verifier.error_0 (= main@%_28_0 (> main@%_5_0 (- 1))))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

