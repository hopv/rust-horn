(set-info :original "3-swap-dec/swap-dec-11-1.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%_34_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 (Array Int Int) )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 (Array Int Int) )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%pa.i.0.pb.i.0_0 Int )
(declare-var main@%pb.i.0.pa.i.0_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%pb.i.2_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 (Array Int Int) )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%pa.i.0_2 Int )
(declare-var main@%pb.i.0_2 Int )
(declare-var main@%pc.i.0_2 Int )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%x.i_0 Int )
(declare-var main@%y.i_0 Int )
(declare-var main@%z.i_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_11_0 (Array Int Int) )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0_0 (Array Int Int) )
(declare-var main@%pa.i.0_0 Int )
(declare-var main@%pb.i.0_0 Int )
(declare-var main@%pc.i.0_0 Int )
(declare-var main@%n.tr.i_0 Int )
(declare-var main@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%pa.i.0_1 Int )
(declare-var main@%pb.i.0_1 Int )
(declare-var main@%pc.i.0_1 Int )
(declare-var main@%n.tr.i_1 Int )
(declare-var main@%pc.i.1_0 Int )
(declare-var main@%pa.i.0.pb.i.0.pb.i.2_0 Int )
(declare-var main@%pb.i.2.pa.i.0.pb.i.0_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%_31_0 (Array Int Int) )
(declare-var main@%_32_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@%shadow.mem.0_2 (Array Int Int) )
(declare-var main@%n.tr.i_2 Int )
(declare-var main@swap_dec_bound_three.exit_0 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@_bb1_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@swap_dec_bound_three.exit_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (> main@%x.i_0 0)
         (> main@%y.i_0 0)
         (> main@%z.i_0 0)
         (distinct main@%x.i_0 main@%y.i_0 main@%z.i_0) ; modified
         (= main@%_1_0 @nd_0)
         (= main@%_3_0 @nd_0)
         (= main@%_5_0 (store main@%_0_0 main@%x.i_0 main@%_4_0))
         (= main@%_6_0 @nd_0)
         (= main@%_8_0 (store main@%_5_0 main@%y.i_0 main@%_7_0))
         (= main@%_9_0 @nd_0)
         (= main@%_11_0 (store main@%_8_0 main@%z.i_0 main@%_10_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_0 main@%_11_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pa.i.0_0 main@%x.i_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pb.i.0_0 main@%y.i_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pc.i.0_0 main@%z.i_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%n.tr.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%shadow.mem.0_1 main@%shadow.mem.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pa.i.0_1 main@%pa.i.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pb.i.0_1 main@%pb.i.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%pc.i.0_1 main@%pc.i.0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%n.tr.i_1 main@%n.tr.i_0)))
    (main@tailrecurse.i
      main@%_4_0
      main@%_2_0
      main@%shadow.mem.0_1
      main@%x.i_0
      main@%n.tr.i_1
      main@%pa.i.0_1
      main@%pb.i.0_1
      main@%pc.i.0_1
      @nd_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%_2_0
                  main@%shadow.mem.0_0
                  main@%x.i_0
                  main@%n.tr.i_0
                  main@%pa.i.0_0
                  main@%pb.i.0_0
                  main@%pc.i.0_0
                  @nd_0)
                true
                (= main@%_12_0 @nd_0)
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%pa.i.0.pb.i.0_0
                   (ite main@%_14_0 main@%pa.i.0_0 main@%pb.i.0_0))
                (= main@%pb.i.0.pa.i.0_0
                   (ite main@%_14_0 main@%pb.i.0_0 main@%pa.i.0_0))
                (= main@%_15_0 @nd_0)
                (= main@%_17_0 (= main@%_16_0 0))
                (= main@%pb.i.2_0
                   (ite main@%_17_0 main@%pb.i.0.pa.i.0_0 main@%pc.i.0_0))
                (= main@%pc.i.1_0
                   (ite main@%_17_0 main@%pc.i.0_0 main@%pb.i.0.pa.i.0_0))
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%pa.i.0.pb.i.0.pb.i.2_0
                   (ite main@%_20_0 main@%pa.i.0.pb.i.0_0 main@%pb.i.2_0))
                (= main@%pb.i.2.pa.i.0.pb.i.0_0
                   (ite main@%_20_0 main@%pb.i.2_0 main@%pa.i.0.pb.i.0_0))
                (= main@%_21_0 (= main@%n.tr.i_0 0))
                (=> main@_bb_0 (and main@_bb_0 main@tailrecurse.i_0))
                (=> (and main@_bb_0 main@tailrecurse.i_0) (not main@%_21_0))
                (=> main@_bb_0
                    (= main@%_23_0
                       (select main@%shadow.mem.0_0
                               main@%pa.i.0.pb.i.0.pb.i.2_0)))
                (=> main@_bb_0 (= main@%_24_0 (+ main@%_23_0 (- 1))))
                (=> main@_bb_0
                    (= main@%_25_0
                       (store main@%shadow.mem.0_0
                              main@%pa.i.0.pb.i.0.pb.i.2_0
                              main@%_24_0)))
                (=> main@_bb_0
                    (= main@%_26_0
                       (select main@%_25_0 main@%pb.i.2.pa.i.0.pb.i.0_0)))
                (=> main@_bb_0 (= main@%_27_0 (+ main@%_26_0 (- 2))))
                (=> main@_bb_0
                    (= main@%_28_0
                       (store main@%_25_0
                              main@%pb.i.2.pa.i.0.pb.i.0_0
                              main@%_27_0)))
                (=> main@_bb_0
                    (= main@%_29_0 (select main@%_28_0 main@%pc.i.1_0)))
                (=> main@_bb_0 (= main@%_30_0 (+ main@%_29_0 (- 3))))
                (=> main@_bb_0
                    (= main@%_31_0
                       (store main@%_28_0 main@%pc.i.1_0 main@%_30_0)))
                (=> main@_bb_0 (= main@%_32_0 (+ main@%n.tr.i_0 (- 1))))
                (=> main@tailrecurse.i_1 (and main@tailrecurse.i_1 main@_bb_0))
                main@tailrecurse.i_1
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%shadow.mem.0_1 main@%_31_0))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pa.i.0_1 main@%pa.i.0.pb.i.0.pb.i.2_0))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pb.i.0_1 main@%pb.i.2.pa.i.0.pb.i.0_0))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pc.i.0_1 main@%pc.i.1_0))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%n.tr.i_1 main@%_32_0))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%shadow.mem.0_2 main@%shadow.mem.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pa.i.0_2 main@%pa.i.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pb.i.0_2 main@%pb.i.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%pc.i.0_2 main@%pc.i.0_1))
                (=> (and main@tailrecurse.i_1 main@_bb_0)
                    (= main@%n.tr.i_2 main@%n.tr.i_1)))))
  (=> a!1
      (main@tailrecurse.i
        main@%_4_0
        main@%_2_0
        main@%shadow.mem.0_2
        main@%x.i_0
        main@%n.tr.i_2
        main@%pa.i.0_2
        main@%pb.i.0_2
        main@%pc.i.0_2
        @nd_0))))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%_2_0
                  main@%shadow.mem.0_0
                  main@%x.i_0
                  main@%n.tr.i_0
                  main@%pa.i.0_0
                  main@%pb.i.0_0
                  main@%pc.i.0_0
                  @nd_0)
                true
                (= main@%_12_0 @nd_0)
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%pa.i.0.pb.i.0_0
                   (ite main@%_14_0 main@%pa.i.0_0 main@%pb.i.0_0))
                (= main@%pb.i.0.pa.i.0_0
                   (ite main@%_14_0 main@%pb.i.0_0 main@%pa.i.0_0))
                (= main@%_15_0 @nd_0)
                (= main@%_17_0 (= main@%_16_0 0))
                (= main@%pb.i.2_0
                   (ite main@%_17_0 main@%pb.i.0.pa.i.0_0 main@%pc.i.0_0))
                (= main@%pc.i.1_0
                   (ite main@%_17_0 main@%pc.i.0_0 main@%pb.i.0.pa.i.0_0))
                (= main@%_18_0 @nd_0)
                (= main@%_20_0 (= main@%_19_0 0))
                (= main@%pa.i.0.pb.i.0.pb.i.2_0
                   (ite main@%_20_0 main@%pa.i.0.pb.i.0_0 main@%pb.i.2_0))
                (= main@%pb.i.2.pa.i.0.pb.i.0_0
                   (ite main@%_20_0 main@%pb.i.2_0 main@%pa.i.0.pb.i.0_0))
                (= main@%_21_0 (= main@%n.tr.i_0 0))
                (=> main@swap_dec_bound_three.exit_0
                    (and main@swap_dec_bound_three.exit_0 main@tailrecurse.i_0))
                (=> (and main@swap_dec_bound_three.exit_0 main@tailrecurse.i_0)
                    main@%_21_0)
                (=> main@swap_dec_bound_three.exit_0
                    (= main@%_33_0 (select main@%shadow.mem.0_0 main@%x.i_0)))
                (=> main@swap_dec_bound_three.exit_0
                    (= main@%_34_0 (< main@%_4_0 main@%_33_0)))
                (=> main@_bb1_0
                    (and main@_bb1_0 main@swap_dec_bound_three.exit_0))
                (=> (and main@_bb1_0 main@swap_dec_bound_three.exit_0)
                    (not main@%_34_0))
                (=> main@_bb1_0 (= main@%_36_0 (- main@%_4_0 main@%_33_0)))
                (=> main@_bb1_0 (= main@%_37_0 (* main@%_2_0 3)))
                (=> main@_bb1_0 (= main@%_38_0 (< main@%_36_0 main@%_37_0)))
                (=> main@_bb1_0 (not main@%_38_0))
                (=> |tuple(main@swap_dec_bound_three.exit_0, main@verifier.error_0)|
                    main@swap_dec_bound_three.exit_0)
                (=> main@verifier.error_0
                    (or (and main@swap_dec_bound_three.exit_0
                             |tuple(main@swap_dec_bound_three.exit_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb1_0)))
                (=> (and main@swap_dec_bound_three.exit_0
                         |tuple(main@swap_dec_bound_three.exit_0, main@verifier.error_0)|)
                    main@%_34_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

