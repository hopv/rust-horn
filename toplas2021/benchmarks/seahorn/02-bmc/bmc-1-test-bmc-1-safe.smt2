(set-info :original "02-bmc/bmc-1-test-bmc-1-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@entry.split ())
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Bool )
(declare-var main@%spec.select.i_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%.12.i_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%spec.select10.i_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%.34.i_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%spec.select11.i_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%_16_0 Int )
(declare-var main@%.56.i_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%spec.select12.i_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%.78.i_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_25_0 Int )
(declare-var main@%spec.select13.i_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@%.9.i_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@entry.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (let ((a!1 (and main@entry
                true
                (= main@%_1_0 (= main@%_0_0 0))
                (= main@%spec.select.i_0 (ite main@%_1_0 1 2))
                (= main@%_3_0 (not (= main@%_2_0 0)))
                (= main@%_4_0 (ite main@%_3_0 1 0))
                (= main@%.12.i_0 (+ main@%spec.select.i_0 main@%_4_0))
                (= main@%_6_0 (not (= main@%_5_0 0)))
                (= main@%_7_0 (ite main@%_6_0 1 0))
                (= main@%spec.select10.i_0 (+ main@%.12.i_0 main@%_7_0))
                (= main@%_9_0 (not (= main@%_8_0 0)))
                (= main@%_10_0 (ite main@%_9_0 1 0))
                (= main@%.34.i_0 (+ main@%spec.select10.i_0 main@%_10_0))
                (= main@%_12_0 (not (= main@%_11_0 0)))
                (= main@%_13_0 (ite main@%_12_0 1 0))
                (= main@%spec.select11.i_0 (+ main@%.34.i_0 main@%_13_0))
                (= main@%_15_0 (not (= main@%_14_0 0)))
                (= main@%_16_0 (ite main@%_15_0 1 0))
                (= main@%.56.i_0 (+ main@%spec.select11.i_0 main@%_16_0))
                (= main@%_18_0 (not (= main@%_17_0 0)))
                (= main@%_19_0 (ite main@%_18_0 1 0))
                (= main@%spec.select12.i_0 (+ main@%.56.i_0 main@%_19_0))
                (= main@%_21_0 (not (= main@%_20_0 0)))
                (= main@%_22_0 (ite main@%_21_0 1 0))
                (= main@%.78.i_0 (+ main@%spec.select12.i_0 main@%_22_0))
                (= main@%_24_0 (not (= main@%_23_0 0)))
                (= main@%_25_0 (ite main@%_24_0 1 0))
                (= main@%spec.select13.i_0 (+ main@%.78.i_0 main@%_25_0))
                (= main@%_27_0 (not (= main@%_26_0 0)))
                (= main@%_28_0 (ite main@%_27_0 1 0))
                (= main@%.9.i_0 (+ main@%spec.select13.i_0 main@%_28_0))
                (= main@%_29_0 (< main@%.9.i_0 12))
                (not main@%_29_0)
                (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
                main@entry.split_0)))
  (=> a!1 main@entry.split)))
(query main@entry.split)
