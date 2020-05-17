(set-info :original "5-swap2-dec/swap2-dec-3-exact-unsafe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int (Array Int Int) Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%_45_0 Bool )
(declare-var main@%_41_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 (Array Int Int) )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_11_0 (Array Int Int) )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_16_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast8_0 Int )
(declare-var main@%.06_2 Int )
(declare-var main@%.0_2 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_15_0 (Array Int Int) )
(declare-var main@%_17_0 (Array Int Int) )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem1.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.06_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%.tr.i_0 Int )
(declare-var main@%shadow.mem1.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.06_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%.tr.i_1 Int )
(declare-var main@%.06..0_0 Int )
(declare-var main@%.0..06_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%_28_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem1.1_0 (Array Int Int) )
(declare-var main@%shadow.mem1.1_1 (Array Int Int) )
(declare-var main@%shadow.mem1.1_2 (Array Int Int) )
(declare-var main@_bb2_0 Bool )
(declare-var main@%_38_0 (Array Int Int) )
(declare-var main@%_39_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem1.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%.tr.i_2 Int )
(declare-var main@swap2_dec_bound.exit_0 Bool )
(declare-var main@%_40_0 Int )
(declare-var main@_bb3_0 Bool )
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
         (> main@%_2_0 0)
         (> main@%_3_0 0)
         (> main@%_4_0 0)
         (> main@%_5_0 0)
         (= main@%_6_0 @nd_0)
         (= main@%_8_0 main@%_2_0)
         (= main@%_9_0 @nd_0)
         (= main@%_11_0 (store main@%_0_0 main@%_2_0 main@%_10_0))
         (= main@%_12_0 main@%_3_0)
         (= main@%_13_0 @nd_0)
         (= main@%_15_0 (store main@%_11_0 main@%_3_0 main@%_14_0))
         (= main@%.0.sroa_cast_0 main@%_4_0)
         (= main@%_16_0 (store main@%_1_0 main@%_4_0 main@%_2_0))
         (= main@%.0.sroa_cast8_0 main@%_5_0)
         (= main@%_17_0 (store main@%_16_0 main@%_5_0 main@%_3_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_0 main@%_17_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_0 main@%_15_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.06_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_0 main@%_5_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr.i_0 main@%_7_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_1 main@%shadow.mem1.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.06_1 main@%.06_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_1 main@%.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr.i_1 main@%.tr.i_0)))
    (main@tailrecurse.i
      main@%_10_0
      main@%_7_0
      main@%shadow.mem.0_1
      main@%_2_0
      main@%.tr.i_1
      main@%shadow.mem1.0_1
      main@%.06_1
      main@%.0_1
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_10_0
                  main@%_7_0
                  main@%shadow.mem.0_0
                  main@%_2_0
                  main@%.tr.i_0
                  main@%shadow.mem1.0_0
                  main@%.06_0
                  main@%.0_0
                  @nd_0)
                true
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%.06..0_0 (ite main@%_20_0 main@%.06_0 main@%.0_0))
                (= main@%.0..06_0 (ite main@%_20_0 main@%.0_0 main@%.06_0))
                (= main@%_21_0 @nd_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_23_0))
                (=> main@_bb_0
                    (= main@%_25_0
                       (select main@%shadow.mem1.0_0 main@%.06..0_0)))
                (=> main@_bb_0
                    (= main@%_26_0
                       (select main@%shadow.mem1.0_0 main@%.0..06_0)))
                (=> main@_bb_0
                    (= main@%_27_0
                       (store main@%shadow.mem1.0_0 main@%.06..0_0 main@%_26_0)))
                (=> main@_bb_0
                    (= main@%_28_0
                       (store main@%_27_0 main@%.0..06_0 main@%_25_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_0 main@%_28_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_23_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_1 main@%shadow.mem1.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_29_0 (= main@%.tr.i_0 0)))
                (=> main@_bb2_0 (and main@_bb2_0 main@may_swap.exit.i_0))
                (=> (and main@_bb2_0 main@may_swap.exit.i_0) (not main@%_29_0))
                (=> main@_bb2_0
                    (= main@%_31_0
                       (select main@%shadow.mem1.1_2 main@%.06..0_0)))
                (=> main@_bb2_0
                    (= main@%_32_0 (select main@%shadow.mem.0_0 main@%_31_0)))
                (=> main@_bb2_0 (= main@%_33_0 (+ main@%_32_0 (- 1))))
                (=> main@_bb2_0
                    (= main@%_34_0
                       (store main@%shadow.mem.0_0 main@%_31_0 main@%_33_0)))
                (=> main@_bb2_0
                    (= main@%_35_0
                       (select main@%shadow.mem1.1_2 main@%.0..06_0)))
                (=> main@_bb2_0
                    (= main@%_36_0 (select main@%_34_0 main@%_35_0)))
                (=> main@_bb2_0 (= main@%_37_0 (+ main@%_36_0 (- 2))))
                (=> main@_bb2_0
                    (= main@%_38_0 (store main@%_34_0 main@%_35_0 main@%_37_0)))
                (=> main@_bb2_0 (= main@%_39_0 (+ main@%.tr.i_0 (- 1))))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_bb2_0))
                main@tailrecurse.i_1
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem1.0_1 main@%shadow.mem1.1_2))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem.0_1 main@%_38_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.06_1 main@%.06..0_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.0_1 main@%.0..06_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.tr.i_1 main@%_39_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem1.0_2 main@%shadow.mem1.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.06_2 main@%.06_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.0_2 main@%.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.tr.i_2 main@%.tr.i_1)))))
  (=> a!1
      (main@tailrecurse.i
        main@%_10_0
        main@%_7_0
        main@%shadow.mem.0_2
        main@%_2_0
        main@%.tr.i_2
        main@%shadow.mem1.0_2
        main@%.06_2
        main@%.0_2
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_10_0
                  main@%_7_0
                  main@%shadow.mem.0_0
                  main@%_2_0
                  main@%.tr.i_0
                  main@%shadow.mem1.0_0
                  main@%.06_0
                  main@%.0_0
                  @nd_0)
                true
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%.06..0_0 (ite main@%_20_0 main@%.06_0 main@%.0_0))
                (= main@%.0..06_0 (ite main@%_20_0 main@%.0_0 main@%.06_0))
                (= main@%_21_0 @nd_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_23_0))
                (=> main@_bb_0
                    (= main@%_25_0
                       (select main@%shadow.mem1.0_0 main@%.06..0_0)))
                (=> main@_bb_0
                    (= main@%_26_0
                       (select main@%shadow.mem1.0_0 main@%.0..06_0)))
                (=> main@_bb_0
                    (= main@%_27_0
                       (store main@%shadow.mem1.0_0 main@%.06..0_0 main@%_26_0)))
                (=> main@_bb_0
                    (= main@%_28_0
                       (store main@%_27_0 main@%.0..06_0 main@%_25_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_0 main@%_28_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_23_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_1 main@%shadow.mem1.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem1.1_2 main@%shadow.mem1.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_29_0 (= main@%.tr.i_0 0)))
                (=> main@swap2_dec_bound.exit_0
                    (and main@swap2_dec_bound.exit_0 main@may_swap.exit.i_0))
                (=> (and main@swap2_dec_bound.exit_0 main@may_swap.exit.i_0)
                    main@%_29_0)
                (=> main@swap2_dec_bound.exit_0
                    (= main@%_40_0 (select main@%shadow.mem.0_0 main@%_2_0)))
                (=> main@swap2_dec_bound.exit_0
                    (= main@%_41_0 (< main@%_10_0 main@%_40_0)))
                (=> main@_bb3_0 (and main@_bb3_0 main@swap2_dec_bound.exit_0))
                (=> (and main@_bb3_0 main@swap2_dec_bound.exit_0)
                    (not main@%_41_0))
                (=> main@_bb3_0 (= main@%_43_0 (- main@%_10_0 main@%_40_0)))
                (=> main@_bb3_0 (= main@%_44_0 (* main@%_7_0 2)))
                (=> main@_bb3_0 (= main@%_45_0 (< main@%_43_0 main@%_44_0)))
                (=> main@_bb3_0 (not main@%_45_0))
                (=> |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|
                    main@swap2_dec_bound.exit_0)
                (=> main@verifier.error_0
                    (or (and main@swap2_dec_bound.exit_0
                             |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb3_0)))
                (=> (and main@swap2_dec_bound.exit_0
                         |tuple(main@swap2_dec_bound.exit_0, main@verifier.error_0)|)
                    main@%_41_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

