(set-info :original "4-swap-dec/swap-dec-1-base-safe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int Int ))
(declare-rel main@swap_dec.exit.split ())
(declare-var main@%_27_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%.0..0512_2 Int )
(declare-var main@%.05..011_2 Int )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast8_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_8_0 (Array Int Int) )
(declare-var main@%_11_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0..0510_0 Int )
(declare-var main@%.05..09_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%.0..0512_0 Int )
(declare-var main@%.05..011_0 Int )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%.0..0512_1 Int )
(declare-var main@%.05..011_1 Int )
(declare-var main@swap_dec.exit_0 Bool )
(declare-var main@%.0.7_0 Int )
(declare-var main@%.0.7_1 Int )
(declare-var main@swap_dec.exit.split_0 Bool )
(declare-var main@%_20_0 (Array Int Int) )
(declare-var main@%.05..0_0 Int )
(declare-var main@%.0..05_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@swap_dec.exit.loopexit_0 Bool )
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
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_3_0 @nd_0)
                (= main@%_5_0 (store main@%_0_0 main@%_1_0 main@%_4_0))
                (= main@%.0.sroa_cast8_0 main@%_2_0)
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (store main@%_5_0 main@%_2_0 main@%_7_0))
                (= main@%_9_0 @nd_0)
                (= main@%_11_0 (= main@%_10_0 0))
                (= main@%_12_0 @nd_0)
                (= main@%_14_0 (= main@%_13_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) main@%_14_0)
                (=> main@.lr.ph_0
                    (= main@%.0..0510_0 (ite main@%_11_0 main@%_2_0 main@%_1_0)))
                (=> main@.lr.ph_0
                    (= main@%.05..09_0 (ite main@%_11_0 main@%_1_0 main@%_2_0)))
                (=> main@tailrecurse.i_0
                    (and main@tailrecurse.i_0 main@.lr.ph_0))
                main@tailrecurse.i_0
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0_0 main@%_8_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.0..0512_0 main@%.0..0510_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.05..011_0 main@%.05..09_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.0..0512_1 main@%.0..0512_0))
                (=> (and main@tailrecurse.i_0 main@.lr.ph_0)
                    (= main@%.05..011_1 main@%.05..011_0)))))
  (=> a!1
      (main@tailrecurse.i
        main@%_4_0
        main@%_1_0
        main@%shadow.mem.0_1
        main@%.05..011_1
        main@%.0..0512_1
        @nd_0))))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_3_0 @nd_0)
                (= main@%_5_0 (store main@%_0_0 main@%_1_0 main@%_4_0))
                (= main@%.0.sroa_cast8_0 main@%_2_0)
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (store main@%_5_0 main@%_2_0 main@%_7_0))
                (= main@%_9_0 @nd_0)
                (= main@%_11_0 (= main@%_10_0 0))
                (= main@%_12_0 @nd_0)
                (= main@%_14_0 (= main@%_13_0 0))
                (=> main@swap_dec.exit_0
                    (and main@swap_dec.exit_0 main@entry_0))
                (=> (and main@swap_dec.exit_0 main@entry_0) (not main@%_14_0))
                (=> (and main@swap_dec.exit_0 main@entry_0)
                    (= main@%.0.7_0 main@%_4_0))
                (=> (and main@swap_dec.exit_0 main@entry_0)
                    (= main@%.0.7_1 main@%.0.7_0))
                (=> main@swap_dec.exit_0
                    (= main@%_27_0 (< main@%_4_0 main@%.0.7_1)))
                (=> main@swap_dec.exit_0 main@%_27_0)
                (=> main@swap_dec.exit.split_0
                    (and main@swap_dec.exit.split_0 main@swap_dec.exit_0))
                main@swap_dec.exit.split_0)))
  (=> a!1 main@swap_dec.exit.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_4_0
           main@%_1_0
           main@%shadow.mem.0_0
           main@%.05..011_0
           main@%.0..0512_0
           @nd_0)
         true
         (= main@%_15_0 (select main@%shadow.mem.0_0 main@%.05..011_0))
         (= main@%_16_0 (+ main@%_15_0 (- 1)))
         (= main@%_17_0
            (store main@%shadow.mem.0_0 main@%.05..011_0 main@%_16_0))
         (= main@%_18_0 (select main@%_17_0 main@%.0..0512_0))
         (= main@%_19_0 (+ main@%_18_0 (- 2)))
         (= main@%_20_0 (store main@%_17_0 main@%.0..0512_0 main@%_19_0))
         (= main@%_21_0 @nd_0)
         (= main@%_23_0 (= main@%_22_0 0))
         (= main@%.05..0_0 (ite main@%_23_0 main@%.05..011_0 main@%.0..0512_0))
         (= main@%.0..05_0 (ite main@%_23_0 main@%.0..0512_0 main@%.05..011_0))
         (= main@%_24_0 @nd_0)
         (= main@%_26_0 (= main@%_25_0 0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         main@tailrecurse.i_1
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) main@%_26_0)
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_1 main@%_20_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0..0512_1 main@%.0..05_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.05..011_1 main@%.05..0_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.0..0512_2 main@%.0..0512_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%.05..011_2 main@%.05..011_1)))
    (main@tailrecurse.i
      main@%_4_0
      main@%_1_0
      main@%shadow.mem.0_2
      main@%.05..011_2
      main@%.0..0512_2
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%_1_0
                  main@%shadow.mem.0_0
                  main@%.05..011_0
                  main@%.0..0512_0
                  @nd_0)
                true
                (= main@%_15_0 (select main@%shadow.mem.0_0 main@%.05..011_0))
                (= main@%_16_0 (+ main@%_15_0 (- 1)))
                (= main@%_17_0
                   (store main@%shadow.mem.0_0 main@%.05..011_0 main@%_16_0))
                (= main@%_18_0 (select main@%_17_0 main@%.0..0512_0))
                (= main@%_19_0 (+ main@%_18_0 (- 2)))
                (= main@%_20_0 (store main@%_17_0 main@%.0..0512_0 main@%_19_0))
                (= main@%_21_0 @nd_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (= main@%.05..0_0
                   (ite main@%_23_0 main@%.05..011_0 main@%.0..0512_0))
                (= main@%.0..05_0
                   (ite main@%_23_0 main@%.0..0512_0 main@%.05..011_0))
                (= main@%_24_0 @nd_0)
                (= main@%_26_0 (= main@%_25_0 0))
                (=> main@swap_dec.exit.loopexit_0
                    (and main@swap_dec.exit.loopexit_0 main@tailrecurse.i_0))
                (=> (and main@swap_dec.exit.loopexit_0 main@tailrecurse.i_0)
                    (not main@%_26_0))
                (=> main@swap_dec.exit.loopexit_0
                    (= main@%.0.7.pre_0 (select main@%_20_0 main@%_1_0)))
                (=> main@swap_dec.exit_0
                    (and main@swap_dec.exit_0 main@swap_dec.exit.loopexit_0))
                (=> (and main@swap_dec.exit_0 main@swap_dec.exit.loopexit_0)
                    (= main@%.0.7_0 main@%.0.7.pre_0))
                (=> (and main@swap_dec.exit_0 main@swap_dec.exit.loopexit_0)
                    (= main@%.0.7_1 main@%.0.7_0))
                (=> main@swap_dec.exit_0
                    (= main@%_27_0 (< main@%_4_0 main@%.0.7_1)))
                (=> main@swap_dec.exit_0 main@%_27_0)
                (=> main@swap_dec.exit.split_0
                    (and main@swap_dec.exit.split_0 main@swap_dec.exit_0))
                main@swap_dec.exit.split_0)))
  (=> a!1 main@swap_dec.exit.split)))
(query main@swap_dec.exit.split)

