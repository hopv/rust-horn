(set-info :original "05-swap-dec/swap-dec-3-exact-safe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int Int (Array Int Int) Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_26_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_25_0 Bool )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%.0..0513_2 Int )
(declare-var main@%.05..012_2 Int )
(declare-var main@%.tr.i11_2 Int )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_3_0 Int )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast8_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_10_0 (Array Int Int) )
(declare-var main@%_13_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0..0510_0 Int )
(declare-var main@%.05..09_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.0..0513_0 Int )
(declare-var main@%.05..012_0 Int )
(declare-var main@%.tr.i11_0 Int )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.0..0513_1 Int )
(declare-var main@%.05..012_1 Int )
(declare-var main@%.tr.i11_1 Int )
(declare-var main@swap_dec_bound.exit_0 Bool )
(declare-var main@%.0.7_0 Int )
(declare-var main@%.0.7_1 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_20_0 (Array Int Int) )
(declare-var main@%_21_0 Int )
(declare-var main@%.05..0_0 Int )
(declare-var main@%.0..05_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@swap_dec_bound.exit.loopexit_0 Bool )
(declare-var main@%.0.7.pre_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (distinct main@%_1_0 main@%_2_0) ; modify
                (= main@%_3_0 @nd_0)
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_5_0 @nd_0)
                (= main@%_7_0 (store main@%_0_0 main@%_1_0 main@%_6_0))
                (= main@%.0.sroa_cast8_0 main@%_2_0)
                (= main@%_8_0 @nd_0)
                (= main@%_10_0 (store main@%_7_0 main@%_2_0 main@%_9_0))
                (= main@%_11_0 @nd_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (= main@%_14_0 (= main@%_4_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) (not main@%_14_0))
                (=> main@.lr.ph_0
                    (= main@%.0..0510_0 (ite main@%_13_0 main@%_2_0 main@%_1_0)))
                (=> main@.lr.ph_0
                    (= main@%.05..09_0 (ite main@%_13_0 main@%_1_0 main@%_2_0)))
                (=> main@tailrecurse.i_0
                    (and main@tailrecurse.i_0 main@.lr.ph_0))
                main@tailrecurse.i_0
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0_0 main@%_10_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.0..0513_0 main@%.0..0510_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.05..012_0 main@%.05..09_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.tr.i11_0 main@%_4_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.0..0513_1 main@%.0..0513_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.05..012_1 main@%.05..012_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.tr.i11_1 main@%.tr.i11_0)))))
  (=> a!1
      (main@tailrecurse.i
        main@%_6_0
        main@%_4_0
        main@%_1_0
        main@%shadow.mem.0_1
        main@%.05..012_1
        main@%.0..0513_1
        main@%.tr.i11_1
        @nd_0))))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (distinct main@%_1_0 main@%_2_0) ; modify
                (= main@%_3_0 @nd_0)
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_5_0 @nd_0)
                (= main@%_7_0 (store main@%_0_0 main@%_1_0 main@%_6_0))
                (= main@%.0.sroa_cast8_0 main@%_2_0)
                (= main@%_8_0 @nd_0)
                (= main@%_10_0 (store main@%_7_0 main@%_2_0 main@%_9_0))
                (= main@%_11_0 @nd_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (= main@%_14_0 (= main@%_4_0 0))
                (=> main@swap_dec_bound.exit_0
                    (and main@swap_dec_bound.exit_0 main@entry_0))
                (=> (and main@swap_dec_bound.exit_0 main@entry_0) main@%_14_0)
                (=> (and main@swap_dec_bound.exit_0 main@entry_0)
                    (= main@%.0.7_0 main@%_6_0))
                (=> (and main@swap_dec_bound.exit_0 main@entry_0)
                    (= main@%.0.7_1 main@%.0.7_0))
                (=> main@swap_dec_bound.exit_0
                    (= main@%_26_0 (< main@%_6_0 main@%.0.7_1)))
                (=> main@_bb_0 (and main@_bb_0 main@swap_dec_bound.exit_0))
                (=> (and main@_bb_0 main@swap_dec_bound.exit_0)
                    (not main@%_26_0))
                (=> main@_bb_0 (= main@%_28_0 (- main@%_6_0 main@%.0.7_1)))
                (=> main@_bb_0 (= main@%_29_0 (* main@%_4_0 2)))
                (=> main@_bb_0 (= main@%_30_0 (> main@%_28_0 main@%_29_0)))
                (=> main@_bb_0 main@%_30_0)
                (=> |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|
                    main@swap_dec_bound.exit_0)
                (=> main@verifier.error_0
                    (or (and main@swap_dec_bound.exit_0
                             |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb_0)))
                (=> (and main@swap_dec_bound.exit_0
                         |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|)
                    main@%_26_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_6_0
           main@%_4_0
           main@%_1_0
           main@%shadow.mem.0_0
           main@%.05..012_0
           main@%.0..0513_0
           main@%.tr.i11_0
           @nd_0)
         true
         (= main@%_15_0 (select main@%shadow.mem.0_0 main@%.05..012_0))
         (= main@%_16_0 (+ main@%_15_0 (- 1)))
         (= main@%_17_0
            (store main@%shadow.mem.0_0 main@%.05..012_0 main@%_16_0))
         (= main@%_18_0 (select main@%_17_0 main@%.0..0513_0))
         (= main@%_19_0 (+ main@%_18_0 (- 2)))
         (= main@%_20_0 (store main@%_17_0 main@%.0..0513_0 main@%_19_0))
         (= main@%_21_0 (+ main@%.tr.i11_0 (- 1)))
         (= main@%_22_0 @nd_0)
         (= main@%_24_0 (= main@%_23_0 0))
         (= main@%.05..0_0 (ite main@%_24_0 main@%.05..012_0 main@%.0..0513_0))
         (= main@%.0..05_0 (ite main@%_24_0 main@%.0..0513_0 main@%.05..012_0))
         (= main@%_25_0 (= main@%_21_0 0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         main@tailrecurse.i_1
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_25_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_1 main@%_20_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0..0513_1 main@%.0..05_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.05..012_1 main@%.05..0_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr.i11_1 main@%_21_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0..0513_2 main@%.0..0513_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.05..012_2 main@%.05..012_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.tr.i11_2 main@%.tr.i11_1)))
    (main@tailrecurse.i
      main@%_6_0
      main@%_4_0
      main@%_1_0
      main@%shadow.mem.0_2
      main@%.05..012_2
      main@%.0..0513_2
      main@%.tr.i11_2
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_6_0
                  main@%_4_0
                  main@%_1_0
                  main@%shadow.mem.0_0
                  main@%.05..012_0
                  main@%.0..0513_0
                  main@%.tr.i11_0
                  @nd_0)
                true
                (= main@%_15_0 (select main@%shadow.mem.0_0 main@%.05..012_0))
                (= main@%_16_0 (+ main@%_15_0 (- 1)))
                (= main@%_17_0
                   (store main@%shadow.mem.0_0 main@%.05..012_0 main@%_16_0))
                (= main@%_18_0 (select main@%_17_0 main@%.0..0513_0))
                (= main@%_19_0 (+ main@%_18_0 (- 2)))
                (= main@%_20_0 (store main@%_17_0 main@%.0..0513_0 main@%_19_0))
                (= main@%_21_0 (+ main@%.tr.i11_0 (- 1)))
                (= main@%_22_0 @nd_0)
                (= main@%_24_0 (= main@%_23_0 0))
                (= main@%.05..0_0
                   (ite main@%_24_0 main@%.05..012_0 main@%.0..0513_0))
                (= main@%.0..05_0
                   (ite main@%_24_0 main@%.0..0513_0 main@%.05..012_0))
                (= main@%_25_0 (= main@%_21_0 0))
                (=> main@swap_dec_bound.exit.loopexit_0
                    (and main@swap_dec_bound.exit.loopexit_0
                         main@tailrecurse.i_0))
                (=> (and main@swap_dec_bound.exit.loopexit_0
                         main@tailrecurse.i_0)
                    main@%_25_0)
                (=> main@swap_dec_bound.exit.loopexit_0
                    (= main@%.0.7.pre_0 (select main@%_20_0 main@%_1_0)))
                (=> main@swap_dec_bound.exit_0
                    (and main@swap_dec_bound.exit_0
                         main@swap_dec_bound.exit.loopexit_0))
                (=> (and main@swap_dec_bound.exit_0
                         main@swap_dec_bound.exit.loopexit_0)
                    (= main@%.0.7_0 main@%.0.7.pre_0))
                (=> (and main@swap_dec_bound.exit_0
                         main@swap_dec_bound.exit.loopexit_0)
                    (= main@%.0.7_1 main@%.0.7_0))
                (=> main@swap_dec_bound.exit_0
                    (= main@%_26_0 (< main@%_6_0 main@%.0.7_1)))
                (=> main@_bb_0 (and main@_bb_0 main@swap_dec_bound.exit_0))
                (=> (and main@_bb_0 main@swap_dec_bound.exit_0)
                    (not main@%_26_0))
                (=> main@_bb_0 (= main@%_28_0 (- main@%_6_0 main@%.0.7_1)))
                (=> main@_bb_0 (= main@%_29_0 (* main@%_4_0 2)))
                (=> main@_bb_0 (= main@%_30_0 (> main@%_28_0 main@%_29_0)))
                (=> main@_bb_0 main@%_30_0)
                (=> |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|
                    main@swap_dec_bound.exit_0)
                (=> main@verifier.error_0
                    (or (and main@swap_dec_bound.exit_0
                             |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb_0)))
                (=> (and main@swap_dec_bound.exit_0
                         |tuple(main@swap_dec_bound.exit_0, main@verifier.error_0)|)
                    main@%_26_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

