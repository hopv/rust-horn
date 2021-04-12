(set-info :original "06-swap2-dec/swap2-dec-4-exact3-safe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_76_0 Int )
(declare-var main@%_77_0 Int )
(declare-var main@%_78_0 Bool )
(declare-var main@%_74_0 Bool )
(declare-var main@%_60_0 Int )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@%_63_0 (Array Int Int) )
(declare-var main@%_64_0 Int )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Int )
(declare-var main@%_67_0 (Array Int Int) )
(declare-var main@%_68_0 Int )
(declare-var main@%_69_0 Int )
(declare-var main@%_70_0 Int )
(declare-var main@%_58_0 Bool )
(declare-var main@%_54_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%_56_0 (Array Int Int) )
(declare-var main@%_50_0 Int )
(declare-var main@%_51_0 Int )
(declare-var main@%_52_0 Bool )
(declare-var main@%_46_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 (Array Int Int) )
(declare-var main@%_42_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Bool )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 (Array Int Int) )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%.018..016_0 Int )
(declare-var main@%.016..018_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%.2_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Bool )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_13_0 (Array Int Int) )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_22_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast21_0 Int )
(declare-var main@%_23_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast22_0 Int )
(declare-var main@%.018_2 Int )
(declare-var main@%.016_2 Int )
(declare-var main@%.0_2 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_21_0 (Array Int Int) )
(declare-var main@%_24_0 (Array Int Int) )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem1.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.018_0 Int )
(declare-var main@%.016_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%.tr.i_0 Int )
(declare-var main@%shadow.mem1.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.018_1 Int )
(declare-var main@%.016_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%.tr.i_1 Int )
(declare-var main@%.1_0 Int )
(declare-var main@%.018..016..2_0 Int )
(declare-var main@%.2..018..016_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%_41_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem1.1_0 (Array Int Int) )
(declare-var main@%shadow.mem1.1_1 (Array Int Int) )
(declare-var main@%shadow.mem1.1_2 (Array Int Int) )
(declare-var main@_bb2_0 Bool )
(declare-var main@%_49_0 (Array Int Int) )
(declare-var main@may_swap.exit3.i_0 Bool )
(declare-var |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)| Bool )
(declare-var main@%shadow.mem1.2_0 (Array Int Int) )
(declare-var main@%shadow.mem1.2_1 (Array Int Int) )
(declare-var main@%shadow.mem1.2_2 (Array Int Int) )
(declare-var main@_bb3_0 Bool )
(declare-var main@%_57_0 (Array Int Int) )
(declare-var main@may_swap.exit4.i_0 Bool )
(declare-var |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)| Bool )
(declare-var main@%shadow.mem1.3_0 (Array Int Int) )
(declare-var main@%shadow.mem1.3_1 (Array Int Int) )
(declare-var main@%shadow.mem1.3_2 (Array Int Int) )
(declare-var main@_bb4_0 Bool )
(declare-var main@%_71_0 (Array Int Int) )
(declare-var main@%_72_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem1.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%.tr.i_2 Int )
(declare-var main@swap2_dec_bound_three.exit_0 Bool )
(declare-var main@%_73_0 Int )
(declare-var main@_bb5_0 Bool )
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
         (> main@%_2_0 0)
         (> main@%_3_0 0)
         (> main@%_4_0 0)
         (> main@%_5_0 0)
         (> main@%_6_0 0)
         (> main@%_7_0 0)
         (= main@%_8_0 @nd_0)
         (= main@%_10_0 main@%_2_0)
         (= main@%_11_0 @nd_0)
         (= main@%_13_0 (store main@%_0_0 main@%_2_0 main@%_12_0))
         (= main@%_14_0 main@%_3_0)
         (= main@%_15_0 @nd_0)
         (= main@%_17_0 (store main@%_13_0 main@%_3_0 main@%_16_0))
         (= main@%_18_0 main@%_4_0)
         (= main@%_19_0 @nd_0)
         (= main@%_21_0 (store main@%_17_0 main@%_4_0 main@%_20_0))
         (= main@%.0.sroa_cast_0 main@%_5_0)
         (= main@%_22_0 (store main@%_1_0 main@%_5_0 main@%_2_0))
         (= main@%.0.sroa_cast21_0 main@%_6_0)
         (= main@%_23_0 (store main@%_22_0 main@%_6_0 main@%_3_0))
         (= main@%.0.sroa_cast22_0 main@%_7_0)
         (= main@%_24_0 (store main@%_23_0 main@%_7_0 main@%_4_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_0 main@%_24_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_0 main@%_21_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.018_0 main@%_5_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.016_0 main@%_6_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_0 main@%_7_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr.i_0 main@%_9_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_1 main@%shadow.mem1.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.018_1 main@%.018_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.016_1 main@%.016_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_1 main@%.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr.i_1 main@%.tr.i_0)))
    (main@tailrecurse.i
      main@%_12_0
      main@%_9_0
      main@%shadow.mem.0_1
      main@%_2_0
      main@%.tr.i_1
      main@%shadow.mem1.0_1
      main@%.018_1
      main@%.016_1
      main@%.0_1
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_12_0
                  main@%_9_0
                  main@%shadow.mem.0_0
                  main@%_2_0
                  main@%.tr.i_0
                  main@%shadow.mem1.0_0
                  main@%.018_0
                  main@%.016_0
                  main@%.0_0
                  @nd_0)
                true
                (= main@%_25_0 @nd_0)
                (= main@%_27_0 (= main@%_26_0 0))
                (= main@%.018..016_0
                   (ite main@%_27_0 main@%.018_0 main@%.016_0))
                (= main@%.016..018_0
                   (ite main@%_27_0 main@%.016_0 main@%.018_0))
                (= main@%_28_0 @nd_0)
                (= main@%_30_0 (= main@%_29_0 0))
                (= main@%.2_0 (ite main@%_30_0 main@%.016..018_0 main@%.0_0))
                (= main@%.1_0 (ite main@%_30_0 main@%.0_0 main@%.016..018_0))
                (= main@%_31_0 @nd_0)
                (= main@%_33_0 (= main@%_32_0 0))
                (= main@%.018..016..2_0
                   (ite main@%_33_0 main@%.018..016_0 main@%.2_0))
                (= main@%.2..018..016_0
                   (ite main@%_33_0 main@%.2_0 main@%.018..016_0))
                (= main@%_34_0 @nd_0)
                (= main@%_36_0 (= main@%_35_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_36_0))
                (=> main@_bb_0
                    (= main@%_38_0
                       (select main@%shadow.mem1.0_0 main@%.018..016..2_0)))
                (=> main@_bb_0
                    (= main@%_39_0
                       (select main@%shadow.mem1.0_0 main@%.2..018..016_0)))
                (=> main@_bb_0
                    (= main@%_40_0
                       (store main@%shadow.mem1.0_0
                              main@%.018..016..2_0
                              main@%_39_0)))
                (=> main@_bb_0
                    (= main@%_41_0
                       (store main@%_40_0 main@%.2..018..016_0 main@%_38_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_0 main@%_41_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_36_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_1 main@%shadow.mem1.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_42_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_44_0 (= main@%_43_0 0)))
                (=> main@_bb2_0 (and main@_bb2_0 main@may_swap.exit.i_0))
                (=> (and main@_bb2_0 main@may_swap.exit.i_0) (not main@%_44_0))
                (=> main@_bb2_0
                    (= main@%_46_0
                       (select main@%shadow.mem1.1_2 main@%.2..018..016_0)))
                (=> main@_bb2_0
                    (= main@%_47_0 (select main@%shadow.mem1.1_2 main@%.1_0)))
                (=> main@_bb2_0
                    (= main@%_48_0
                       (store main@%shadow.mem1.1_2
                              main@%.2..018..016_0
                              main@%_47_0)))
                (=> main@_bb2_0
                    (= main@%_49_0 (store main@%_48_0 main@%.1_0 main@%_46_0)))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@may_swap.exit.i_0)
                (=> main@may_swap.exit3.i_0
                    (or (and main@may_swap.exit3.i_0 main@_bb2_0)
                        (and main@may_swap.exit.i_0
                             |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)))
                (=> (and main@may_swap.exit3.i_0 main@_bb2_0)
                    (= main@%shadow.mem1.2_0 main@%_49_0))
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    main@%_44_0)
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    (= main@%shadow.mem1.2_1 main@%shadow.mem1.1_2))
                (=> (and main@may_swap.exit3.i_0 main@_bb2_0)
                    (= main@%shadow.mem1.2_2 main@%shadow.mem1.2_0))
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    (= main@%shadow.mem1.2_2 main@%shadow.mem1.2_1))
                (=> main@may_swap.exit3.i_0 (= main@%_50_0 @nd_0))
                (=> main@may_swap.exit3.i_0 (= main@%_52_0 (= main@%_51_0 0)))
                (=> main@_bb3_0 (and main@_bb3_0 main@may_swap.exit3.i_0))
                (=> (and main@_bb3_0 main@may_swap.exit3.i_0) (not main@%_52_0))
                (=> main@_bb3_0
                    (= main@%_54_0
                       (select main@%shadow.mem1.2_2 main@%.018..016..2_0)))
                (=> main@_bb3_0
                    (= main@%_55_0
                       (select main@%shadow.mem1.2_2 main@%.2..018..016_0)))
                (=> main@_bb3_0
                    (= main@%_56_0
                       (store main@%shadow.mem1.2_2
                              main@%.018..016..2_0
                              main@%_55_0)))
                (=> main@_bb3_0
                    (= main@%_57_0
                       (store main@%_56_0 main@%.2..018..016_0 main@%_54_0)))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@may_swap.exit3.i_0)
                (=> main@may_swap.exit4.i_0
                    (or (and main@may_swap.exit4.i_0 main@_bb3_0)
                        (and main@may_swap.exit3.i_0
                             |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)))
                (=> (and main@may_swap.exit4.i_0 main@_bb3_0)
                    (= main@%shadow.mem1.3_0 main@%_57_0))
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    main@%_52_0)
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    (= main@%shadow.mem1.3_1 main@%shadow.mem1.2_2))
                (=> (and main@may_swap.exit4.i_0 main@_bb3_0)
                    (= main@%shadow.mem1.3_2 main@%shadow.mem1.3_0))
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    (= main@%shadow.mem1.3_2 main@%shadow.mem1.3_1))
                (=> main@may_swap.exit4.i_0 (= main@%_58_0 (= main@%.tr.i_0 0)))
                (=> main@_bb4_0 (and main@_bb4_0 main@may_swap.exit4.i_0))
                (=> (and main@_bb4_0 main@may_swap.exit4.i_0) (not main@%_58_0))
                (=> main@_bb4_0
                    (= main@%_60_0
                       (select main@%shadow.mem1.3_2 main@%.018..016..2_0)))
                (=> main@_bb4_0
                    (= main@%_61_0 (select main@%shadow.mem.0_0 main@%_60_0)))
                (=> main@_bb4_0 (= main@%_62_0 (+ main@%_61_0 (- 1))))
                (=> main@_bb4_0
                    (= main@%_63_0
                       (store main@%shadow.mem.0_0 main@%_60_0 main@%_62_0)))
                (=> main@_bb4_0
                    (= main@%_64_0
                       (select main@%shadow.mem1.3_2 main@%.2..018..016_0)))
                (=> main@_bb4_0
                    (= main@%_65_0 (select main@%_63_0 main@%_64_0)))
                (=> main@_bb4_0 (= main@%_66_0 (+ main@%_65_0 (- 2))))
                (=> main@_bb4_0
                    (= main@%_67_0 (store main@%_63_0 main@%_64_0 main@%_66_0)))
                (=> main@_bb4_0
                    (= main@%_68_0 (select main@%shadow.mem1.3_2 main@%.1_0)))
                (=> main@_bb4_0
                    (= main@%_69_0 (select main@%_67_0 main@%_68_0)))
                (=> main@_bb4_0 (= main@%_70_0 (+ main@%_69_0 (- 3))))
                (=> main@_bb4_0
                    (= main@%_71_0 (store main@%_67_0 main@%_68_0 main@%_70_0)))
                (=> main@_bb4_0 (= main@%_72_0 (+ main@%.tr.i_0 (- 1))))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_bb4_0))
                main@tailrecurse.i_1
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%shadow.mem1.0_1 main@%shadow.mem1.3_2))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%shadow.mem.0_1 main@%_71_0))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.018_1 main@%.018..016..2_0))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.016_1 main@%.2..018..016_0))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.0_1 main@%.1_0))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.tr.i_1 main@%_72_0))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%shadow.mem1.0_2 main@%shadow.mem1.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.018_2 main@%.018_1))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.016_2 main@%.016_1))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.0_2 main@%.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb4_0)
                    (= main@%.tr.i_2 main@%.tr.i_1)))))
  (=> a!1
      (main@tailrecurse.i
        main@%_12_0
        main@%_9_0
        main@%shadow.mem.0_2
        main@%_2_0
        main@%.tr.i_2
        main@%shadow.mem1.0_2
        main@%.018_2
        main@%.016_2
        main@%.0_2
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_12_0
                  main@%_9_0
                  main@%shadow.mem.0_0
                  main@%_2_0
                  main@%.tr.i_0
                  main@%shadow.mem1.0_0
                  main@%.018_0
                  main@%.016_0
                  main@%.0_0
                  @nd_0)
                true
                (= main@%_25_0 @nd_0)
                (= main@%_27_0 (= main@%_26_0 0))
                (= main@%.018..016_0
                   (ite main@%_27_0 main@%.018_0 main@%.016_0))
                (= main@%.016..018_0
                   (ite main@%_27_0 main@%.016_0 main@%.018_0))
                (= main@%_28_0 @nd_0)
                (= main@%_30_0 (= main@%_29_0 0))
                (= main@%.2_0 (ite main@%_30_0 main@%.016..018_0 main@%.0_0))
                (= main@%.1_0 (ite main@%_30_0 main@%.0_0 main@%.016..018_0))
                (= main@%_31_0 @nd_0)
                (= main@%_33_0 (= main@%_32_0 0))
                (= main@%.018..016..2_0
                   (ite main@%_33_0 main@%.018..016_0 main@%.2_0))
                (= main@%.2..018..016_0
                   (ite main@%_33_0 main@%.2_0 main@%.018..016_0))
                (= main@%_34_0 @nd_0)
                (= main@%_36_0 (= main@%_35_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_36_0))
                (=> main@_bb_0
                    (= main@%_38_0
                       (select main@%shadow.mem1.0_0 main@%.018..016..2_0)))
                (=> main@_bb_0
                    (= main@%_39_0
                       (select main@%shadow.mem1.0_0 main@%.2..018..016_0)))
                (=> main@_bb_0
                    (= main@%_40_0
                       (store main@%shadow.mem1.0_0
                              main@%.018..016..2_0
                              main@%_39_0)))
                (=> main@_bb_0
                    (= main@%_41_0
                       (store main@%_40_0 main@%.2..018..016_0 main@%_38_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_0 main@%_41_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_36_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_1 main@%shadow.mem1.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_42_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_44_0 (= main@%_43_0 0)))
                (=> main@_bb2_0 (and main@_bb2_0 main@may_swap.exit.i_0))
                (=> (and main@_bb2_0 main@may_swap.exit.i_0) (not main@%_44_0))
                (=> main@_bb2_0
                    (= main@%_46_0
                       (select main@%shadow.mem1.1_2 main@%.2..018..016_0)))
                (=> main@_bb2_0
                    (= main@%_47_0 (select main@%shadow.mem1.1_2 main@%.1_0)))
                (=> main@_bb2_0
                    (= main@%_48_0
                       (store main@%shadow.mem1.1_2
                              main@%.2..018..016_0
                              main@%_47_0)))
                (=> main@_bb2_0
                    (= main@%_49_0 (store main@%_48_0 main@%.1_0 main@%_46_0)))
                (=> |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|
                    main@may_swap.exit.i_0)
                (=> main@may_swap.exit3.i_0
                    (or (and main@may_swap.exit3.i_0 main@_bb2_0)
                        (and main@may_swap.exit.i_0
                             |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)))
                (=> (and main@may_swap.exit3.i_0 main@_bb2_0)
                    (= main@%shadow.mem1.2_0 main@%_49_0))
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    main@%_44_0)
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    (= main@%shadow.mem1.2_1 main@%shadow.mem1.1_2))
                (=> (and main@may_swap.exit3.i_0 main@_bb2_0)
                    (= main@%shadow.mem1.2_2 main@%shadow.mem1.2_0))
                (=> (and main@may_swap.exit.i_0
                         |tuple(main@may_swap.exit.i_0, main@may_swap.exit3.i_0)|)
                    (= main@%shadow.mem1.2_2 main@%shadow.mem1.2_1))
                (=> main@may_swap.exit3.i_0 (= main@%_50_0 @nd_0))
                (=> main@may_swap.exit3.i_0 (= main@%_52_0 (= main@%_51_0 0)))
                (=> main@_bb3_0 (and main@_bb3_0 main@may_swap.exit3.i_0))
                (=> (and main@_bb3_0 main@may_swap.exit3.i_0) (not main@%_52_0))
                (=> main@_bb3_0
                    (= main@%_54_0
                       (select main@%shadow.mem1.2_2 main@%.018..016..2_0)))
                (=> main@_bb3_0
                    (= main@%_55_0
                       (select main@%shadow.mem1.2_2 main@%.2..018..016_0)))
                (=> main@_bb3_0
                    (= main@%_56_0
                       (store main@%shadow.mem1.2_2
                              main@%.018..016..2_0
                              main@%_55_0)))
                (=> main@_bb3_0
                    (= main@%_57_0
                       (store main@%_56_0 main@%.2..018..016_0 main@%_54_0)))
                (=> |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|
                    main@may_swap.exit3.i_0)
                (=> main@may_swap.exit4.i_0
                    (or (and main@may_swap.exit4.i_0 main@_bb3_0)
                        (and main@may_swap.exit3.i_0
                             |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)))
                (=> (and main@may_swap.exit4.i_0 main@_bb3_0)
                    (= main@%shadow.mem1.3_0 main@%_57_0))
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    main@%_52_0)
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    (= main@%shadow.mem1.3_1 main@%shadow.mem1.2_2))
                (=> (and main@may_swap.exit4.i_0 main@_bb3_0)
                    (= main@%shadow.mem1.3_2 main@%shadow.mem1.3_0))
                (=> (and main@may_swap.exit3.i_0
                         |tuple(main@may_swap.exit3.i_0, main@may_swap.exit4.i_0)|)
                    (= main@%shadow.mem1.3_2 main@%shadow.mem1.3_1))
                (=> main@may_swap.exit4.i_0 (= main@%_58_0 (= main@%.tr.i_0 0)))
                (=> main@swap2_dec_bound_three.exit_0
                    (and main@swap2_dec_bound_three.exit_0
                         main@may_swap.exit4.i_0))
                (=> (and main@swap2_dec_bound_three.exit_0
                         main@may_swap.exit4.i_0)
                    main@%_58_0)
                (=> main@swap2_dec_bound_three.exit_0
                    (= main@%_73_0 (select main@%shadow.mem.0_0 main@%_2_0)))
                (=> main@swap2_dec_bound_three.exit_0
                    (= main@%_74_0 (< main@%_12_0 main@%_73_0)))
                (=> main@_bb5_0
                    (and main@_bb5_0 main@swap2_dec_bound_three.exit_0))
                (=> (and main@_bb5_0 main@swap2_dec_bound_three.exit_0)
                    (not main@%_74_0))
                (=> main@_bb5_0 (= main@%_76_0 (- main@%_12_0 main@%_73_0)))
                (=> main@_bb5_0 (= main@%_77_0 (* main@%_9_0 3)))
                (=> main@_bb5_0 (= main@%_78_0 (> main@%_76_0 main@%_77_0)))
                (=> main@_bb5_0 main@%_78_0)
                (=> |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|
                    main@swap2_dec_bound_three.exit_0)
                (=> main@verifier.error_0
                    (or (and main@swap2_dec_bound_three.exit_0
                             |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb5_0)))
                (=> (and main@swap2_dec_bound_three.exit_0
                         |tuple(main@swap2_dec_bound_three.exit_0, main@verifier.error_0)|)
                    main@%_74_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

