(set-info :original "05-swap-dec/swap-dec-2-base3-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@swap_dec_three.exit.split ())
(declare-var main@%_40_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select19_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Bool )
(declare-var main@%.2_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%spec.select2130_2 Int )
(declare-var main@%spec.select2029_2 Int )
(declare-var main@%.128_2 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast17_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast18_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%spec.select22_0 Int )
(declare-var main@%spec.select1923_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%.224_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@tailrecurse.i.preheader_0 Bool )
(declare-var main@%spec.select2127_0 Int )
(declare-var main@%spec.select2026_0 Int )
(declare-var main@%.125_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%spec.select2130_0 Int )
(declare-var main@%spec.select2029_0 Int )
(declare-var main@%.128_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%spec.select2130_1 Int )
(declare-var main@%spec.select2029_1 Int )
(declare-var main@%.128_1 Int )
(declare-var main@swap_dec_three.exit_0 Bool )
(declare-var main@%.0.16_0 Int )
(declare-var main@%.0.16_1 Int )
(declare-var main@swap_dec_three.exit.split_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%.1_0 Int )
(declare-var main@%spec.select20_0 Int )
(declare-var main@%spec.select21_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@swap_dec_three.exit.loopexit_0 Bool )
(declare-var main@%.0.16.pre_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (> main@%_3_0 0)
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_4_0 @nd_0)
                (= main@%sm_0 (store main@%sm6_0 main@%_1_0 main@%_5_0))
                (= main@%.0.sroa_cast17_0 main@%_2_0)
                (= main@%_6_0 @nd_0)
                (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_7_0))
                (= main@%.0.sroa_cast18_0 main@%_3_0)
                (= main@%_8_0 @nd_0)
                (= main@%sm2_0 (store main@%sm1_0 main@%_3_0 main@%_9_0))
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%spec.select22_0
                   (ite main@%_12_0 main@%_1_0 main@%_2_0))
                (= main@%spec.select1923_0
                   (ite main@%_12_0 main@%_2_0 main@%_1_0))
                (= main@%_13_0 @nd_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (= main@%.224_0
                   (ite main@%_15_0 main@%spec.select1923_0 main@%_3_0))
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@tailrecurse.i.preheader_0
                    (and main@tailrecurse.i.preheader_0 main@entry_0))
                (=> (and main@tailrecurse.i.preheader_0 main@entry_0)
                    main@%_21_0)
                (=> main@tailrecurse.i.preheader_0
                    (= main@%spec.select2127_0
                       (ite main@%_18_0 main@%.224_0 main@%spec.select22_0)))
                (=> main@tailrecurse.i.preheader_0
                    (= main@%spec.select2026_0
                       (ite main@%_18_0 main@%spec.select22_0 main@%.224_0)))
                (=> main@tailrecurse.i.preheader_0
                    (= main@%.125_0
                       (ite main@%_15_0 main@%_3_0 main@%spec.select1923_0)))
                (=> main@tailrecurse.i_0
                    (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%shadow.mem.0.0_0 main@%sm2_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select2130_0 main@%spec.select2127_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select2029_0 main@%spec.select2026_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%.128_0 main@%.125_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select2130_1 main@%spec.select2130_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select2029_1 main@%spec.select2029_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%.128_1 main@%.128_0))
                main@tailrecurse.i_0)))
  (=> a!1
      (main@tailrecurse.i
        main@%_5_0
        main@%_1_0
        main@%shadow.mem.0.0_1
        main@%spec.select2029_1
        main@%spec.select2130_1
        main@%.128_1
        @nd_0
        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (> main@%_3_0 0)
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_4_0 @nd_0)
                (= main@%sm_0 (store main@%sm6_0 main@%_1_0 main@%_5_0))
                (= main@%.0.sroa_cast17_0 main@%_2_0)
                (= main@%_6_0 @nd_0)
                (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_7_0))
                (= main@%.0.sroa_cast18_0 main@%_3_0)
                (= main@%_8_0 @nd_0)
                (= main@%sm2_0 (store main@%sm1_0 main@%_3_0 main@%_9_0))
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%spec.select22_0
                   (ite main@%_12_0 main@%_1_0 main@%_2_0))
                (= main@%spec.select1923_0
                   (ite main@%_12_0 main@%_2_0 main@%_1_0))
                (= main@%_13_0 @nd_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (= main@%.224_0
                   (ite main@%_15_0 main@%spec.select1923_0 main@%_3_0))
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@swap_dec_three.exit_0
                    (and main@swap_dec_three.exit_0 main@entry_0))
                (=> (and main@swap_dec_three.exit_0 main@entry_0)
                    (not main@%_21_0))
                (=> (and main@swap_dec_three.exit_0 main@entry_0)
                    (= main@%.0.16_0 main@%_5_0))
                (=> (and main@swap_dec_three.exit_0 main@entry_0)
                    (= main@%.0.16_1 main@%.0.16_0))
                (=> main@swap_dec_three.exit_0
                    (= main@%_40_0 (< main@%_5_0 main@%.0.16_1)))
                (=> main@swap_dec_three.exit_0 main@%_40_0)
                (=> main@swap_dec_three.exit.split_0
                    (and main@swap_dec_three.exit.split_0
                         main@swap_dec_three.exit_0))
                main@swap_dec_three.exit.split_0)))
  (=> a!1 main@swap_dec_three.exit.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_5_0
           main@%_1_0
           main@%shadow.mem.0.0_0
           main@%spec.select2029_0
           main@%spec.select2130_0
           main@%.128_0
           @nd_0
           main@%loop.bound_0)
         true
         (= main@%_22_0 (select main@%shadow.mem.0.0_0 main@%spec.select2029_0))
         (= main@%_23_0 (+ main@%_22_0 (- 1)))
         (= main@%sm3_0
            (store main@%shadow.mem.0.0_0 main@%spec.select2029_0 main@%_23_0))
         (= main@%_24_0 (select main@%sm3_0 main@%spec.select2130_0))
         (= main@%_25_0 (+ main@%_24_0 (- 2)))
         (= main@%sm4_0 (store main@%sm3_0 main@%spec.select2130_0 main@%_25_0))
         (= main@%_26_0 (select main@%sm4_0 main@%.128_0))
         (= main@%_27_0 (+ main@%_26_0 (- 3)))
         (= main@%sm5_0 (store main@%sm4_0 main@%.128_0 main@%_27_0))
         (= main@%_28_0 @nd_0)
         (= main@%_30_0 (= main@%_29_0 0))
         (= main@%spec.select_0
            (ite main@%_30_0 main@%spec.select2029_0 main@%spec.select2130_0))
         (= main@%spec.select19_0
            (ite main@%_30_0 main@%spec.select2130_0 main@%spec.select2029_0))
         (= main@%_31_0 @nd_0)
         (= main@%_33_0 (= main@%_32_0 0))
         (= main@%.2_0 (ite main@%_33_0 main@%spec.select19_0 main@%.128_0))
         (= main@%.1_0 (ite main@%_33_0 main@%.128_0 main@%spec.select19_0))
         (= main@%_34_0 @nd_0)
         (= main@%_36_0 (= main@%_35_0 0))
         (= main@%spec.select20_0
            (ite main@%_36_0 main@%spec.select_0 main@%.2_0))
         (= main@%spec.select21_0
            (ite main@%_36_0 main@%.2_0 main@%spec.select_0))
         (= main@%_37_0 @nd_0)
         (= main@%_39_0 (= main@%_38_0 main@%loop.bound_0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) main@%_39_0)
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_1 main@%sm5_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select2130_1 main@%spec.select21_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select2029_1 main@%spec.select20_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.128_1 main@%.1_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select2130_2 main@%spec.select2130_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select2029_2 main@%spec.select2029_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.128_2 main@%.128_1))
         main@tailrecurse.i_1)
    (main@tailrecurse.i
      main@%_5_0
      main@%_1_0
      main@%shadow.mem.0.0_2
      main@%spec.select2029_2
      main@%spec.select2130_2
      main@%.128_2
      @nd_0
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_5_0
                  main@%_1_0
                  main@%shadow.mem.0.0_0
                  main@%spec.select2029_0
                  main@%spec.select2130_0
                  main@%.128_0
                  @nd_0
                  main@%loop.bound_0)
                true
                (= main@%_22_0
                   (select main@%shadow.mem.0.0_0 main@%spec.select2029_0))
                (= main@%_23_0 (+ main@%_22_0 (- 1)))
                (= main@%sm3_0
                   (store main@%shadow.mem.0.0_0
                          main@%spec.select2029_0
                          main@%_23_0))
                (= main@%_24_0 (select main@%sm3_0 main@%spec.select2130_0))
                (= main@%_25_0 (+ main@%_24_0 (- 2)))
                (= main@%sm4_0
                   (store main@%sm3_0 main@%spec.select2130_0 main@%_25_0))
                (= main@%_26_0 (select main@%sm4_0 main@%.128_0))
                (= main@%_27_0 (+ main@%_26_0 (- 3)))
                (= main@%sm5_0 (store main@%sm4_0 main@%.128_0 main@%_27_0))
                (= main@%_28_0 @nd_0)
                (= main@%_30_0 (= main@%_29_0 0))
                (= main@%spec.select_0
                   (ite main@%_30_0
                        main@%spec.select2029_0
                        main@%spec.select2130_0))
                (= main@%spec.select19_0
                   (ite main@%_30_0
                        main@%spec.select2130_0
                        main@%spec.select2029_0))
                (= main@%_31_0 @nd_0)
                (= main@%_33_0 (= main@%_32_0 0))
                (= main@%.2_0
                   (ite main@%_33_0 main@%spec.select19_0 main@%.128_0))
                (= main@%.1_0
                   (ite main@%_33_0 main@%.128_0 main@%spec.select19_0))
                (= main@%_34_0 @nd_0)
                (= main@%_36_0 (= main@%_35_0 0))
                (= main@%spec.select20_0
                   (ite main@%_36_0 main@%spec.select_0 main@%.2_0))
                (= main@%spec.select21_0
                   (ite main@%_36_0 main@%.2_0 main@%spec.select_0))
                (= main@%_37_0 @nd_0)
                (= main@%_39_0 (= main@%_38_0 main@%loop.bound_0))
                (=> main@swap_dec_three.exit.loopexit_0
                    (and main@swap_dec_three.exit.loopexit_0
                         main@tailrecurse.i_0))
                (=> (and main@swap_dec_three.exit.loopexit_0
                         main@tailrecurse.i_0)
                    (not main@%_39_0))
                (=> main@swap_dec_three.exit.loopexit_0
                    (= main@%.0.16.pre_0 (select main@%sm5_0 main@%_1_0)))
                (=> main@swap_dec_three.exit_0
                    (and main@swap_dec_three.exit_0
                         main@swap_dec_three.exit.loopexit_0))
                (=> (and main@swap_dec_three.exit_0
                         main@swap_dec_three.exit.loopexit_0)
                    (= main@%.0.16_0 main@%.0.16.pre_0))
                (=> (and main@swap_dec_three.exit_0
                         main@swap_dec_three.exit.loopexit_0)
                    (= main@%.0.16_1 main@%.0.16_0))
                (=> main@swap_dec_three.exit_0
                    (= main@%_40_0 (< main@%_5_0 main@%.0.16_1)))
                (=> main@swap_dec_three.exit_0 main@%_40_0)
                (=> main@swap_dec_three.exit.split_0
                    (and main@swap_dec_three.exit.split_0
                         main@swap_dec_three.exit_0))
                main@swap_dec_three.exit.split_0)))
  (=> a!1 main@swap_dec_three.exit.split)))
(query main@swap_dec_three.exit.split)

