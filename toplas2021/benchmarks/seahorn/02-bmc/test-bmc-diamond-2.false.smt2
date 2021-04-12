(set-info :original "02-bmc/test-bmc-diamond-2.false.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@_bb ())
(declare-rel main@_bb2 ())
(declare-rel main@_bb4 ())
(declare-rel main@_bb6 ())
(declare-rel main@_bb8 ())
(declare-rel main@_bb10 ())
(declare-rel main@verifier.error.split ())
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@_bb_0 Bool )
(declare-var main@_bb_1 Bool )
(declare-var main@_bb1_0 Bool )
(declare-var main@_bb2_0 Bool )
(declare-var main@_bb2_1 Bool )
(declare-var main@_bb3_0 Bool )
(declare-var main@_bb4_0 Bool )
(declare-var main@_bb4_1 Bool )
(declare-var main@_bb5_0 Bool )
(declare-var main@_bb6_0 Bool )
(declare-var main@_bb6_1 Bool )
(declare-var main@_bb7_0 Bool )
(declare-var main@_bb8_0 Bool )
(declare-var main@_bb8_1 Bool )
(declare-var main@_bb9_0 Bool )
(declare-var main@_bb10_0 Bool )
(declare-var main@_bb10_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (=> main@_bb_0 (and main@_bb_0 main@entry_0))
         main@_bb_0)
    main@_bb))
(rule (=> (and main@_bb
         true
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_3_0)))
    main@_bb))
(rule (=> (and main@_bb
         true
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@_bb1_0 (and main@_bb1_0 main@_bb_0))
         (=> (and main@_bb1_0 main@_bb_0) main@%_3_0)
         (=> main@_bb2_0 (and main@_bb2_0 main@_bb1_0))
         main@_bb2_0)
    main@_bb2))
(rule (=> (and main@_bb2
         true
         (= main@%_8_0 (= main@%_7_0 0))
         (=> main@_bb2_1 (and main@_bb2_1 main@_bb2_0))
         main@_bb2_1
         (=> (and main@_bb2_1 main@_bb2_0) (not main@%_8_0)))
    main@_bb2))
(rule (=> (and main@_bb2
         true
         (= main@%_8_0 (= main@%_7_0 0))
         (=> main@_bb3_0 (and main@_bb3_0 main@_bb2_0))
         (=> (and main@_bb3_0 main@_bb2_0) main@%_8_0)
         (=> main@_bb4_0 (and main@_bb4_0 main@_bb3_0))
         main@_bb4_0)
    main@_bb4))
(rule (=> (and main@_bb4
         true
         (= main@%_13_0 (= main@%_12_0 0))
         (=> main@_bb4_1 (and main@_bb4_1 main@_bb4_0))
         main@_bb4_1
         (=> (and main@_bb4_1 main@_bb4_0) (not main@%_13_0)))
    main@_bb4))
(rule (=> (and main@_bb4
         true
         (= main@%_13_0 (= main@%_12_0 0))
         (=> main@_bb5_0 (and main@_bb5_0 main@_bb4_0))
         (=> (and main@_bb5_0 main@_bb4_0) main@%_13_0)
         (=> main@_bb6_0 (and main@_bb6_0 main@_bb5_0))
         main@_bb6_0)
    main@_bb6))
(rule (=> (and main@_bb6
         true
         (= main@%_18_0 (= main@%_17_0 0))
         (=> main@_bb6_1 (and main@_bb6_1 main@_bb6_0))
         main@_bb6_1
         (=> (and main@_bb6_1 main@_bb6_0) (not main@%_18_0)))
    main@_bb6))
(rule (=> (and main@_bb6
         true
         (= main@%_18_0 (= main@%_17_0 0))
         (=> main@_bb7_0 (and main@_bb7_0 main@_bb6_0))
         (=> (and main@_bb7_0 main@_bb6_0) main@%_18_0)
         (=> main@_bb8_0 (and main@_bb8_0 main@_bb7_0))
         main@_bb8_0)
    main@_bb8))
(rule (=> (and main@_bb8
         true
         (= main@%_23_0 (= main@%_22_0 0))
         (=> main@_bb8_1 (and main@_bb8_1 main@_bb8_0))
         main@_bb8_1
         (=> (and main@_bb8_1 main@_bb8_0) (not main@%_23_0)))
    main@_bb8))
(rule (=> (and main@_bb8
         true
         (= main@%_23_0 (= main@%_22_0 0))
         (=> main@_bb9_0 (and main@_bb9_0 main@_bb8_0))
         (=> (and main@_bb9_0 main@_bb8_0) main@%_23_0)
         (=> main@_bb10_0 (and main@_bb10_0 main@_bb9_0))
         main@_bb10_0)
    main@_bb10))
(rule (=> (and main@_bb10
         true
         (= main@%_28_0 (= main@%_27_0 0))
         (=> main@_bb10_1 (and main@_bb10_1 main@_bb10_0))
         main@_bb10_1
         (=> (and main@_bb10_1 main@_bb10_0) (not main@%_28_0)))
    main@_bb10))
(rule (=> (and main@_bb10
         true
         (= main@%_28_0 (= main@%_27_0 0))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@_bb10_0))
         (=> (and main@verifier.error_0 main@_bb10_0) main@%_28_0)
         true
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(query main@verifier.error.split)

