(set-info :original "06-swap2-dec/swap2-dec-1-base-safe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i ((Array Int Int) (Array Int Int) Int Int Int Int Int ))
(declare-rel main@swap2_dec.exit.split ())
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 (Array Int Int) )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 Bool )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 (Array Int Int) )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 (Array Int Int) )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_14_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast8_0 Int )
(declare-var main@%.06_2 Int )
(declare-var main@%.0_2 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_13_0 (Array Int Int) )
(declare-var main@%_15_0 (Array Int Int) )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem1.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.06_0 Int )
(declare-var main@%.0_0 Int )
(declare-var main@%shadow.mem1.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.06_1 Int )
(declare-var main@%.0_1 Int )
(declare-var main@%.06..0_0 Int )
(declare-var main@%.0..06_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%_26_0 (Array Int Int) )
(declare-var main@may_swap.exit.i_0 Bool )
(declare-var |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)| Bool )
(declare-var main@%shadow.mem.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.1_2 (Array Int Int) )
(declare-var main@_bb2_0 Bool )
(declare-var main@%_38_0 (Array Int Int) )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem1.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@swap2_dec.exit_0 Bool )
(declare-var main@swap2_dec.exit.split_0 Bool )
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
         (distinct main@%_2_0 main@%_3_0 main@%_4_0 main@%_5_0) ; modify
         (= main@%_6_0 main@%_2_0)
         (= main@%_7_0 @nd_0)
         (= main@%_9_0 (store main@%_1_0 main@%_2_0 main@%_8_0))
         (= main@%_10_0 main@%_3_0)
         (= main@%_11_0 @nd_0)
         (= main@%_13_0 (store main@%_9_0 main@%_3_0 main@%_12_0))
         (= main@%.0.sroa_cast_0 main@%_4_0)
         (= main@%_14_0 (store main@%_0_0 main@%_4_0 main@%_2_0))
         (= main@%.0.sroa_cast8_0 main@%_5_0)
         (= main@%_15_0 (store main@%_14_0 main@%_5_0 main@%_3_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_0 main@%_13_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_0 main@%_15_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.06_0 main@%_4_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_0 main@%_5_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem1.0_1 main@%shadow.mem1.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.06_1 main@%.06_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (= main@%.0_1 main@%.0_0)))
    (main@tailrecurse.i
      main@%shadow.mem1.0_1
      main@%shadow.mem.0_1
      main@%.06_1
      main@%.0_1
      main@%_2_0
      main@%_8_0
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%shadow.mem1.0_0
                  main@%shadow.mem.0_0
                  main@%.06_0
                  main@%.0_0
                  main@%_2_0
                  main@%_8_0
                  @nd_0)
                true
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (= main@%.06..0_0 (ite main@%_18_0 main@%.06_0 main@%.0_0))
                (= main@%.0..06_0 (ite main@%_18_0 main@%.0_0 main@%.06_0))
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_21_0))
                (=> main@_bb_0
                    (= main@%_23_0 (select main@%shadow.mem.0_0 main@%.06..0_0)))
                (=> main@_bb_0
                    (= main@%_24_0 (select main@%shadow.mem.0_0 main@%.0..06_0)))
                (=> main@_bb_0
                    (= main@%_25_0
                       (store main@%shadow.mem.0_0 main@%.06..0_0 main@%_24_0)))
                (=> main@_bb_0
                    (= main@%_26_0
                       (store main@%_25_0 main@%.0..06_0 main@%_23_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem.1_0 main@%_26_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_21_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem.1_1 main@%shadow.mem.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem.1_2 main@%shadow.mem.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem.1_2 main@%shadow.mem.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_27_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_29_0 (= main@%_28_0 0)))
                (=> main@_bb2_0 (and main@_bb2_0 main@may_swap.exit.i_0))
                (=> (and main@_bb2_0 main@may_swap.exit.i_0) main@%_29_0)
                (=> main@_bb2_0
                    (= main@%_31_0 (select main@%shadow.mem.1_2 main@%.06..0_0)))
                (=> main@_bb2_0
                    (= main@%_32_0 (select main@%shadow.mem1.0_0 main@%_31_0)))
                (=> main@_bb2_0 (= main@%_33_0 (+ main@%_32_0 (- 1))))
                (=> main@_bb2_0
                    (= main@%_34_0
                       (store main@%shadow.mem1.0_0 main@%_31_0 main@%_33_0)))
                (=> main@_bb2_0
                    (= main@%_35_0 (select main@%shadow.mem.1_2 main@%.0..06_0)))
                (=> main@_bb2_0
                    (= main@%_36_0 (select main@%_34_0 main@%_35_0)))
                (=> main@_bb2_0 (= main@%_37_0 (+ main@%_36_0 (- 2))))
                (=> main@_bb2_0
                    (= main@%_38_0 (store main@%_34_0 main@%_35_0 main@%_37_0)))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_bb2_0))
                main@tailrecurse.i_1
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem1.0_1 main@%_38_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem.0_1 main@%shadow.mem.1_2))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.06_1 main@%.06..0_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.0_1 main@%.0..06_0))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem1.0_2 main@%shadow.mem1.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.06_2 main@%.06_1))
                (=> (and main@tailrecurse.i_1 main@_bb2_0)
                    (= main@%.0_2 main@%.0_1)))))
  (=> a!1
      (main@tailrecurse.i
        main@%shadow.mem1.0_2
        main@%shadow.mem.0_2
        main@%.06_2
        main@%.0_2
        main@%_2_0
        main@%_8_0
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%shadow.mem1.0_0
                  main@%shadow.mem.0_0
                  main@%.06_0
                  main@%.0_0
                  main@%_2_0
                  main@%_8_0
                  @nd_0)
                true
                (= main@%_16_0 @nd_0)
                (= main@%_18_0 (= main@%_17_0 0))
                (= main@%.06..0_0 (ite main@%_18_0 main@%.06_0 main@%.0_0))
                (= main@%.0..06_0 (ite main@%_18_0 main@%.0_0 main@%.06_0))
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_21_0))
                (=> main@_bb_0
                    (= main@%_23_0 (select main@%shadow.mem.0_0 main@%.06..0_0)))
                (=> main@_bb_0
                    (= main@%_24_0 (select main@%shadow.mem.0_0 main@%.0..06_0)))
                (=> main@_bb_0
                    (= main@%_25_0
                       (store main@%shadow.mem.0_0 main@%.06..0_0 main@%_24_0)))
                (=> main@_bb_0
                    (= main@%_26_0
                       (store main@%_25_0 main@%.0..06_0 main@%_23_0)))
                (=> |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|
                    main@tailrecurse.i_0)
                (=> main@may_swap.exit.i_0
                    (or (and main@may_swap.exit.i_0 main@_bb_0)
                        (and main@tailrecurse.i_0
                             |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem.1_0 main@%_26_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    main@%_21_0)
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem.1_1 main@%shadow.mem.0_0))
                (=> (and main@may_swap.exit.i_0 main@_bb_0)
                    (= main@%shadow.mem.1_2 main@%shadow.mem.1_0))
                (=> (and main@tailrecurse.i_0
                         |tuple(main@tailrecurse.i_0, main@may_swap.exit.i_0)|)
                    (= main@%shadow.mem.1_2 main@%shadow.mem.1_1))
                (=> main@may_swap.exit.i_0 (= main@%_27_0 @nd_0))
                (=> main@may_swap.exit.i_0 (= main@%_29_0 (= main@%_28_0 0)))
                (=> main@swap2_dec.exit_0
                    (and main@swap2_dec.exit_0 main@may_swap.exit.i_0))
                (=> (and main@swap2_dec.exit_0 main@may_swap.exit.i_0)
                    (not main@%_29_0))
                (=> main@swap2_dec.exit_0
                    (= main@%_39_0 (select main@%shadow.mem1.0_0 main@%_2_0)))
                (=> main@swap2_dec.exit_0
                    (= main@%_40_0 (< main@%_8_0 main@%_39_0)))
                (=> main@swap2_dec.exit_0 main@%_40_0)
                (=> main@swap2_dec.exit.split_0
                    (and main@swap2_dec.exit.split_0 main@swap2_dec.exit_0))
                main@swap2_dec.exit.split_0)))
  (=> a!1 main@swap2_dec.exit.split)))
(query main@swap2_dec.exit.split)

