(set-info :original "5-linger-dec/linger-dec-11-1.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel linger_dec_bound_three@_1 ((Array Int Int) Int Int Int Int Int ))
(declare-rel linger_dec_bound_three@_shadow.mem.0 ((Array Int Int) (Array Int Int) Int Int Int Int Int ))
(declare-rel linger_dec_bound_three (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@verifier.error.split ())
(declare-var linger_dec_bound_three@%_29_0 Int )
(declare-var linger_dec_bound_three@%_25_0 Int )
(declare-var linger_dec_bound_three@%_26_0 Int )
(declare-var linger_dec_bound_three@%_pc.x_0 Bool )
(declare-var linger_dec_bound_three@%_21_0 Int )
(declare-var linger_dec_bound_three@%_22_0 Int )
(declare-var linger_dec_bound_three@%_br5_0 Bool )
(declare-var linger_dec_bound_three@%_5_0 Int )
(declare-var linger_dec_bound_three@%_6_0 Int )
(declare-var linger_dec_bound_three@%_store_0 (Array Int Int) )
(declare-var linger_dec_bound_three@%_8_0 Int )
(declare-var linger_dec_bound_three@%_9_0 Int )
(declare-var linger_dec_bound_three@%_store1_0 (Array Int Int) )
(declare-var linger_dec_bound_three@%_11_0 Int )
(declare-var linger_dec_bound_three@%_12_0 Int )
(declare-var linger_dec_bound_three@%_store2_0 (Array Int Int) )
(declare-var linger_dec_bound_three@%_14_0 Int )
(declare-var linger_dec_bound_three@%_15_0 Int )
(declare-var linger_dec_bound_three@%_17_0 Int )
(declare-var linger_dec_bound_three@%_18_0 Int )
(declare-var linger_dec_bound_three@%_br4_0 Bool )
(declare-var linger_dec_bound_three@%.02_2 Int )
(declare-var linger_dec_bound_three@%.01_2 Int )
(declare-var linger_dec_bound_three@%.0_2 Int )
(declare-var linger_dec_bound_three@%_br_0 Bool )
(declare-var linger_dec_bound_three@%shadow.mem.0_2 (Array Int Int) )
(declare-var linger_dec_bound_three@%_tail_0 (Array Int Int) )
(declare-var linger_dec_bound_three@%shadow.mem.0_0 (Array Int Int) )
(declare-var linger_dec_bound_three@%n_0 Int )
(declare-var linger_dec_bound_three@%pa_0 Int )
(declare-var linger_dec_bound_three@%pb_0 Int )
(declare-var linger_dec_bound_three@%pc_0 Int )
(declare-var @nd_0 Int )
(declare-var linger_dec_bound_three@_1_0 Bool )
(declare-var linger_dec_bound_three@%x_0 Int )
(declare-var linger_dec_bound_three@_call_0 Bool )
(declare-var linger_dec_bound_three@%_store3_0 (Array Int Int) )
(declare-var linger_dec_bound_three@_20_0 Bool )
(declare-var linger_dec_bound_three@_24_0 Bool )
(declare-var linger_dec_bound_three@%pc.x_0 Int )
(declare-var linger_dec_bound_three@_.02_0 Bool )
(declare-var |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)| Bool )
(declare-var |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)| Bool )
(declare-var linger_dec_bound_three@%.02_0 Int )
(declare-var linger_dec_bound_three@%.01_0 Int )
(declare-var linger_dec_bound_three@%.0_0 Int )
(declare-var linger_dec_bound_three@%.02_1 Int )
(declare-var linger_dec_bound_three@%.01_1 Int )
(declare-var linger_dec_bound_three@%.0_1 Int )
(declare-var linger_dec_bound_three@%.02_3 Int )
(declare-var linger_dec_bound_three@%.01_3 Int )
(declare-var linger_dec_bound_three@%.0_3 Int )
(declare-var linger_dec_bound_three@%_call6_0 (Array Int Int) )
(declare-var linger_dec_bound_three@_shadow.mem.0_0 Bool )
(declare-var |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)| Bool )
(declare-var linger_dec_bound_three@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%a.i_0 Int )
(declare-var main@%b.i_0 Int )
(declare-var main@%c.i_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 (Array Int Int) )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 (Array Int Int) )
(declare-var main@%_12_0 (Array Int Int) )
(declare-var main@%_14_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@entry_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (linger_dec_bound_three
  true
  true
  true
  linger_dec_bound_three@%_tail_0
  linger_dec_bound_three@%shadow.mem.0_0
  linger_dec_bound_three@%n_0
  linger_dec_bound_three@%pa_0
  linger_dec_bound_three@%pb_0
  linger_dec_bound_three@%pc_0))
(rule (linger_dec_bound_three
  false
  true
  true
  linger_dec_bound_three@%_tail_0
  linger_dec_bound_three@%shadow.mem.0_0
  linger_dec_bound_three@%n_0
  linger_dec_bound_three@%pa_0
  linger_dec_bound_three@%pb_0
  linger_dec_bound_three@%pc_0))
(rule (linger_dec_bound_three
  false
  false
  false
  linger_dec_bound_three@%_tail_0
  linger_dec_bound_three@%shadow.mem.0_0
  linger_dec_bound_three@%n_0
  linger_dec_bound_three@%pa_0
  linger_dec_bound_three@%pb_0
  linger_dec_bound_three@%pc_0))
(rule (linger_dec_bound_three@_1
  linger_dec_bound_three@%_tail_0
  linger_dec_bound_three@%n_0
  @nd_0
  linger_dec_bound_three@%pc_0
  linger_dec_bound_three@%pb_0
  linger_dec_bound_three@%pa_0))
(rule (let ((a!1 (and (linger_dec_bound_three@_1
                  linger_dec_bound_three@%_tail_0
                  linger_dec_bound_three@%n_0
                  @nd_0
                  linger_dec_bound_three@%pc_0
                  linger_dec_bound_three@%pb_0
                  linger_dec_bound_three@%pa_0)
                true
                (> linger_dec_bound_three@%x_0 0)
                (= linger_dec_bound_three@%_br_0
                   (= linger_dec_bound_three@%n_0 0))
                (=> linger_dec_bound_three@_call_0
                    (and linger_dec_bound_three@_call_0
                         linger_dec_bound_three@_1_0))
                (=> (and linger_dec_bound_three@_call_0
                         linger_dec_bound_three@_1_0)
                    (not linger_dec_bound_three@%_br_0))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_5_0
                       (select linger_dec_bound_three@%_tail_0
                               linger_dec_bound_three@%pa_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_6_0
                       (+ linger_dec_bound_three@%_5_0 (- 1))))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_store_0
                       (store linger_dec_bound_three@%_tail_0
                              linger_dec_bound_three@%pa_0
                              linger_dec_bound_three@%_6_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_8_0
                       (select linger_dec_bound_three@%_store_0
                               linger_dec_bound_three@%pb_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_9_0
                       (+ linger_dec_bound_three@%_8_0 (- 2))))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_store1_0
                       (store linger_dec_bound_three@%_store_0
                              linger_dec_bound_three@%pb_0
                              linger_dec_bound_three@%_9_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_11_0
                       (select linger_dec_bound_three@%_store1_0
                               linger_dec_bound_three@%pc_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_12_0
                       (+ linger_dec_bound_three@%_11_0 (- 3))))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_store2_0
                       (store linger_dec_bound_three@%_store1_0
                              linger_dec_bound_three@%pc_0
                              linger_dec_bound_three@%_12_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_14_0 @nd_0))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_store3_0
                       (store linger_dec_bound_three@%_store2_0
                              linger_dec_bound_three@%x_0
                              linger_dec_bound_three@%_15_0)))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_17_0 @nd_0))
                (=> linger_dec_bound_three@_call_0
                    (= linger_dec_bound_three@%_br4_0
                       (= linger_dec_bound_three@%_18_0 0)))
                (=> linger_dec_bound_three@_20_0
                    (and linger_dec_bound_three@_20_0
                         linger_dec_bound_three@_call_0))
                (=> (and linger_dec_bound_three@_20_0
                         linger_dec_bound_three@_call_0)
                    linger_dec_bound_three@%_br4_0)
                (=> linger_dec_bound_three@_20_0
                    (= linger_dec_bound_three@%_21_0 @nd_0))
                (=> linger_dec_bound_three@_20_0
                    (= linger_dec_bound_three@%_br5_0
                       (= linger_dec_bound_three@%_22_0 0)))
                (=> linger_dec_bound_three@_24_0
                    (and linger_dec_bound_three@_24_0
                         linger_dec_bound_three@_20_0))
                (=> (and linger_dec_bound_three@_24_0
                         linger_dec_bound_three@_20_0)
                    linger_dec_bound_three@%_br5_0)
                (=> linger_dec_bound_three@_24_0
                    (= linger_dec_bound_three@%_25_0 @nd_0))
                (=> linger_dec_bound_three@_24_0
                    (= linger_dec_bound_three@%_pc.x_0
                       (= linger_dec_bound_three@%_26_0 0)))
                (=> linger_dec_bound_three@_24_0
                    (= linger_dec_bound_three@%pc.x_0
                       (ite linger_dec_bound_three@%_pc.x_0
                            linger_dec_bound_three@%pc_0
                            linger_dec_bound_three@%x_0)))
                (=> |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|
                    linger_dec_bound_three@_20_0)
                (=> |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|
                    linger_dec_bound_three@_call_0)
                (=> linger_dec_bound_three@_.02_0
                    (or (and linger_dec_bound_three@_.02_0
                             linger_dec_bound_three@_24_0)
                        (and linger_dec_bound_three@_20_0
                             |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                        (and linger_dec_bound_three@_call_0
                             |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.02_0
                       linger_dec_bound_three@%pb_0))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.01_0
                       linger_dec_bound_three@%pa_0))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.0_0
                       linger_dec_bound_three@%pc.x_0))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (not linger_dec_bound_three@%_br5_0))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.02_1
                       linger_dec_bound_three@%x_0))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.01_1
                       linger_dec_bound_three@%pa_0))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.0_1
                       linger_dec_bound_three@%pc_0))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (not linger_dec_bound_three@%_br4_0))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.02_2
                       linger_dec_bound_three@%pb_0))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.01_2
                       linger_dec_bound_three@%x_0))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.0_2
                       linger_dec_bound_three@%pc_0))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.02_3
                       linger_dec_bound_three@%.02_0))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.01_3
                       linger_dec_bound_three@%.01_0))
                (=> (and linger_dec_bound_three@_.02_0
                         linger_dec_bound_three@_24_0)
                    (= linger_dec_bound_three@%.0_3
                       linger_dec_bound_three@%.0_0))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.02_3
                       linger_dec_bound_three@%.02_1))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.01_3
                       linger_dec_bound_three@%.01_1))
                (=> (and linger_dec_bound_three@_20_0
                         |tuple(linger_dec_bound_three@_20_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.0_3
                       linger_dec_bound_three@%.0_1))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.02_3
                       linger_dec_bound_three@%.02_2))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.01_3
                       linger_dec_bound_three@%.01_2))
                (=> (and linger_dec_bound_three@_call_0
                         |tuple(linger_dec_bound_three@_call_0, linger_dec_bound_three@_.02_0)|)
                    (= linger_dec_bound_three@%.0_3
                       linger_dec_bound_three@%.0_2))
                (=> linger_dec_bound_three@_.02_0
                    (= linger_dec_bound_three@%_29_0
                       (+ linger_dec_bound_three@%n_0 (- 1))))
                (linger_dec_bound_three
                  linger_dec_bound_three@_.02_0
                  false
                  false
                  linger_dec_bound_three@%_store3_0
                  linger_dec_bound_three@%_call6_0
                  linger_dec_bound_three@%_29_0
                  linger_dec_bound_three@%.01_3
                  linger_dec_bound_three@%.02_3
                  linger_dec_bound_three@%.0_3)
                (=> |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)|
                    linger_dec_bound_three@_1_0)
                (=> linger_dec_bound_three@_shadow.mem.0_0
                    (or (and linger_dec_bound_three@_shadow.mem.0_0
                             linger_dec_bound_three@_.02_0)
                        (and linger_dec_bound_three@_1_0
                             |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)|)))
                linger_dec_bound_three@_shadow.mem.0_0
                (=> (and linger_dec_bound_three@_shadow.mem.0_0
                         linger_dec_bound_three@_.02_0)
                    (= linger_dec_bound_three@%shadow.mem.0_0
                       linger_dec_bound_three@%_call6_0))
                (=> (and linger_dec_bound_three@_1_0
                         |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)|)
                    linger_dec_bound_three@%_br_0)
                (=> (and linger_dec_bound_three@_1_0
                         |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)|)
                    (= linger_dec_bound_three@%shadow.mem.0_1
                       linger_dec_bound_three@%_tail_0))
                (=> (and linger_dec_bound_three@_shadow.mem.0_0
                         linger_dec_bound_three@_.02_0)
                    (= linger_dec_bound_three@%shadow.mem.0_2
                       linger_dec_bound_three@%shadow.mem.0_0))
                (=> (and linger_dec_bound_three@_1_0
                         |tuple(linger_dec_bound_three@_1_0, linger_dec_bound_three@_shadow.mem.0_0)|)
                    (= linger_dec_bound_three@%shadow.mem.0_2
                       linger_dec_bound_three@%shadow.mem.0_1)))))
  (=> a!1
      (linger_dec_bound_three@_shadow.mem.0
        linger_dec_bound_three@%_tail_0
        linger_dec_bound_three@%shadow.mem.0_2
        linger_dec_bound_three@%n_0
        @nd_0
        linger_dec_bound_three@%pc_0
        linger_dec_bound_three@%pb_0
        linger_dec_bound_three@%pa_0))))
(rule (=> (linger_dec_bound_three@_shadow.mem.0
      linger_dec_bound_three@%_tail_0
      linger_dec_bound_three@%shadow.mem.0_0
      linger_dec_bound_three@%n_0
      @nd_0
      linger_dec_bound_three@%pc_0
      linger_dec_bound_three@%pb_0
      linger_dec_bound_three@%pa_0)
    (linger_dec_bound_three
      true
      false
      false
      linger_dec_bound_three@%_tail_0
      linger_dec_bound_three@%shadow.mem.0_0
      linger_dec_bound_three@%n_0
      linger_dec_bound_three@%pa_0
      linger_dec_bound_three@%pb_0
      linger_dec_bound_three@%pc_0)))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%a.i_0 0)
                (> main@%b.i_0 0)
                (> main@%c.i_0 0)
                (= main@%_1_0 @nd_0)
                (= main@%_3_0 @nd_0)
                (= main@%_5_0 (store main@%_0_0 main@%a.i_0 main@%_4_0))
                (= main@%_6_0 @nd_0)
                (= main@%_8_0 (store main@%_5_0 main@%b.i_0 main@%_7_0))
                (= main@%_9_0 @nd_0)
                (= main@%_11_0 (store main@%_8_0 main@%c.i_0 main@%_10_0))
                (linger_dec_bound_three
                  true
                  false
                  false
                  main@%_11_0
                  main@%_12_0
                  main@%_2_0
                  main@%a.i_0
                  main@%b.i_0
                  main@%c.i_0)
                (= main@%_13_0 (select main@%_12_0 main@%a.i_0))
                (= main@%_14_0 (< main@%_4_0 main@%_13_0))
                (=> main@_bb_0 (and main@_bb_0 main@entry_0))
                (=> (and main@_bb_0 main@entry_0) (not main@%_14_0))
                (=> main@_bb_0 (= main@%_16_0 (- main@%_4_0 main@%_13_0)))
                (=> main@_bb_0 (= main@%_17_0 (* main@%_2_0 3)))
                (=> main@_bb_0 (= main@%_18_0 (< main@%_16_0 main@%_17_0)))
                (=> main@_bb_0 (not main@%_18_0))
                (=> |tuple(main@entry_0, main@verifier.error_0)| main@entry_0)
                (=> main@verifier.error_0
                    (or (and main@entry_0
                             |tuple(main@entry_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb_0)))
                (=> (and main@entry_0
                         |tuple(main@entry_0, main@verifier.error_0)|)
                    main@%_14_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

