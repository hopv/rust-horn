(set-info :original "02-bmc/bmc-3-test-bmc-3-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@verifier.error.split ())
(declare-var main@%_38_0 Bool )
(declare-var main@%.5.i_2 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Bool )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@_2_0 Bool )
(declare-var main@_3_0 Bool )
(declare-var |tuple(main@entry_0, main@_3_0)| Bool )
(declare-var main@%.0.i_0 Int )
(declare-var main@%.0.i_1 Int )
(declare-var main@%.0.i_2 Int )
(declare-var main@_6_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@_8_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@_10_0 Bool )
(declare-var main@%.1.i_0 Int )
(declare-var main@%.1.i_1 Int )
(declare-var main@%.1.i_2 Int )
(declare-var main@_13_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@_15_0 Bool )
(declare-var main@%_16_0 Int )
(declare-var main@_17_0 Bool )
(declare-var main@%.2.i_0 Int )
(declare-var main@%.2.i_1 Int )
(declare-var main@%.2.i_2 Int )
(declare-var main@_20_0 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@_22_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@_24_0 Bool )
(declare-var main@%.3.i_0 Int )
(declare-var main@%.3.i_1 Int )
(declare-var main@%.3.i_2 Int )
(declare-var main@_27_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@_29_0 Bool )
(declare-var main@%_30_0 Int )
(declare-var main@_31_0 Bool )
(declare-var main@%.4.i_0 Int )
(declare-var main@%.4.i_1 Int )
(declare-var main@%.4.i_2 Int )
(declare-var main@_34_0 Bool )
(declare-var main@%_35_0 Int )
(declare-var main@_36_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.5.i_0 Int )
(declare-var main@%.5.i_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (let ((a!1 (and main@entry
                true
                (= main@%_1_0 (= main@%_0_0 0))
                (=> main@_2_0 (and main@_2_0 main@entry_0))
                (=> (and main@_2_0 main@entry_0) (not main@%_1_0))
                (=> |tuple(main@entry_0, main@_3_0)| main@entry_0)
                (=> main@_3_0
                    (or (and main@_3_0 main@_2_0)
                        |tuple(main@entry_0, main@_3_0)|))
                (=> |tuple(main@entry_0, main@_3_0)| main@%_1_0)
                (=> (and main@_3_0 main@_2_0) (= main@%.0.i_0 1))
                (=> |tuple(main@entry_0, main@_3_0)| (= main@%.0.i_1 2))
                (=> (and main@_3_0 main@_2_0) (= main@%.0.i_2 main@%.0.i_0))
                (=> |tuple(main@entry_0, main@_3_0)|
                    (= main@%.0.i_2 main@%.0.i_1))
                (=> main@_3_0 (= main@%_5_0 (= main@%_4_0 0)))
                (=> main@_6_0 (and main@_6_0 main@_3_0))
                (=> (and main@_6_0 main@_3_0) (not main@%_5_0))
                (=> main@_6_0 (= main@%_7_0 (+ main@%.0.i_2 1)))
                (=> main@_8_0 (and main@_8_0 main@_3_0))
                (=> (and main@_8_0 main@_3_0) main@%_5_0)
                (=> main@_8_0 (= main@%_9_0 (+ main@%.0.i_2 2)))
                (=> main@_10_0
                    (or (and main@_10_0 main@_8_0) (and main@_10_0 main@_6_0)))
                (=> (and main@_10_0 main@_8_0) (= main@%.1.i_0 main@%_9_0))
                (=> (and main@_10_0 main@_6_0) (= main@%.1.i_1 main@%_7_0))
                (=> (and main@_10_0 main@_8_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> (and main@_10_0 main@_6_0) (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_10_0 (= main@%_12_0 (= main@%_11_0 0)))
                (=> main@_13_0 (and main@_13_0 main@_10_0))
                (=> (and main@_13_0 main@_10_0) (not main@%_12_0))
                (=> main@_13_0 (= main@%_14_0 (+ main@%.1.i_2 1)))
                (=> main@_15_0 (and main@_15_0 main@_10_0))
                (=> (and main@_15_0 main@_10_0) main@%_12_0)
                (=> main@_15_0 (= main@%_16_0 (+ main@%.1.i_2 2)))
                (=> main@_17_0
                    (or (and main@_17_0 main@_15_0) (and main@_17_0 main@_13_0)))
                (=> (and main@_17_0 main@_15_0) (= main@%.2.i_0 main@%_16_0))
                (=> (and main@_17_0 main@_13_0) (= main@%.2.i_1 main@%_14_0))
                (=> (and main@_17_0 main@_15_0) (= main@%.2.i_2 main@%.2.i_0))
                (=> (and main@_17_0 main@_13_0) (= main@%.2.i_2 main@%.2.i_1))
                (=> main@_17_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@_20_0 (and main@_20_0 main@_17_0))
                (=> (and main@_20_0 main@_17_0) (not main@%_19_0))
                (=> main@_20_0 (= main@%_21_0 (+ main@%.2.i_2 1)))
                (=> main@_22_0 (and main@_22_0 main@_17_0))
                (=> (and main@_22_0 main@_17_0) main@%_19_0)
                (=> main@_22_0 (= main@%_23_0 (+ main@%.2.i_2 2)))
                (=> main@_24_0
                    (or (and main@_24_0 main@_22_0) (and main@_24_0 main@_20_0)))
                (=> (and main@_24_0 main@_22_0) (= main@%.3.i_0 main@%_23_0))
                (=> (and main@_24_0 main@_20_0) (= main@%.3.i_1 main@%_21_0))
                (=> (and main@_24_0 main@_22_0) (= main@%.3.i_2 main@%.3.i_0))
                (=> (and main@_24_0 main@_20_0) (= main@%.3.i_2 main@%.3.i_1))
                (=> main@_24_0 (= main@%_26_0 (= main@%_25_0 0)))
                (=> main@_27_0 (and main@_27_0 main@_24_0))
                (=> (and main@_27_0 main@_24_0) (not main@%_26_0))
                (=> main@_27_0 (= main@%_28_0 (+ main@%.3.i_2 1)))
                (=> main@_29_0 (and main@_29_0 main@_24_0))
                (=> (and main@_29_0 main@_24_0) main@%_26_0)
                (=> main@_29_0 (= main@%_30_0 (+ main@%.3.i_2 2)))
                (=> main@_31_0
                    (or (and main@_31_0 main@_29_0) (and main@_31_0 main@_27_0)))
                (=> (and main@_31_0 main@_29_0) (= main@%.4.i_0 main@%_30_0))
                (=> (and main@_31_0 main@_27_0) (= main@%.4.i_1 main@%_28_0))
                (=> (and main@_31_0 main@_29_0) (= main@%.4.i_2 main@%.4.i_0))
                (=> (and main@_31_0 main@_27_0) (= main@%.4.i_2 main@%.4.i_1))
                (=> main@_31_0 (= main@%_33_0 (= main@%_32_0 0)))
                (=> main@_34_0 (and main@_34_0 main@_31_0))
                (=> (and main@_34_0 main@_31_0) (not main@%_33_0))
                (=> main@_34_0 (= main@%_35_0 (+ main@%.4.i_2 1)))
                (=> main@_36_0 (and main@_36_0 main@_31_0))
                (=> (and main@_36_0 main@_31_0) main@%_33_0)
                (=> main@_36_0 (= main@%_37_0 (+ main@%.4.i_2 2)))
                (=> main@verifier.error_0
                    (or (and main@verifier.error_0 main@_36_0)
                        (and main@verifier.error_0 main@_34_0)))
                (=> (and main@verifier.error_0 main@_36_0)
                    (= main@%.5.i_0 main@%_37_0))
                (=> (and main@verifier.error_0 main@_34_0)
                    (= main@%.5.i_1 main@%_35_0))
                (=> (and main@verifier.error_0 main@_36_0)
                    (= main@%.5.i_2 main@%.5.i_0))
                (=> (and main@verifier.error_0 main@_34_0)
                    (= main@%.5.i_2 main@%.5.i_1))
                (=> main@verifier.error_0 (= main@%_38_0 (< main@%.5.i_2 13)))
                (=> main@verifier.error_0 (not main@%_38_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)
