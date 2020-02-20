(set-info :original "5-linger-dec/linger-dec-10-0.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel linger_dec_bound@_1 ((Array Int Int) Int Int Int ))
(declare-rel linger_dec_bound@_shadow.mem.0 ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel linger_dec_bound (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@verifier.error.split ())
(declare-var linger_dec_bound@%_5_0 Int )
(declare-var linger_dec_bound@%pa_0 Int )
(declare-var linger_dec_bound@%_6_0 Int )
(declare-var linger_dec_bound@%_store_0 (Array Int Int) )
(declare-var linger_dec_bound@%_8_0 Int )
(declare-var @nd_0 Int )
(declare-var linger_dec_bound@%_9_0 Int )
(declare-var linger_dec_bound@%_store1_0 (Array Int Int) )
(declare-var linger_dec_bound@%_11_0 Int )
(declare-var linger_dec_bound@%_12_0 Int )
(declare-var linger_dec_bound@%_13_0 Int )
(declare-var linger_dec_bound@%_14_0 Bool )
(declare-var linger_dec_bound@%_15_0 Int )
(declare-var linger_dec_bound@%_br_0 Bool )
(declare-var linger_dec_bound@%shadow.mem.0_2 (Array Int Int) )
(declare-var linger_dec_bound@%_tail_0 (Array Int Int) )
(declare-var linger_dec_bound@%shadow.mem.0_0 (Array Int Int) )
(declare-var linger_dec_bound@%n_0 Int )
(declare-var linger_dec_bound@_1_0 Bool )
(declare-var linger_dec_bound@%x_0 Int )
(declare-var linger_dec_bound@_call_0 Bool )
(declare-var linger_dec_bound@%_call2_0 (Array Int Int) )
(declare-var linger_dec_bound@_shadow.mem.0_0 Bool )
(declare-var |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)| Bool )
(declare-var linger_dec_bound@%shadow.mem.0_1 (Array Int Int) )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%_0_0 (Array Int Int) )
(declare-var main@%a.i_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 (Array Int Int) )
(declare-var main@%_6_0 (Array Int Int) )
(declare-var main@%_8_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@entry_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (linger_dec_bound true
                  true
                  true
                  linger_dec_bound@%_tail_0
                  linger_dec_bound@%shadow.mem.0_0
                  linger_dec_bound@%n_0
                  linger_dec_bound@%pa_0))
(rule (linger_dec_bound false
                  true
                  true
                  linger_dec_bound@%_tail_0
                  linger_dec_bound@%shadow.mem.0_0
                  linger_dec_bound@%n_0
                  linger_dec_bound@%pa_0))
(rule (linger_dec_bound false
                  false
                  false
                  linger_dec_bound@%_tail_0
                  linger_dec_bound@%shadow.mem.0_0
                  linger_dec_bound@%n_0
                  linger_dec_bound@%pa_0))
(rule (linger_dec_bound@_1
  linger_dec_bound@%_tail_0
  linger_dec_bound@%pa_0
  @nd_0
  linger_dec_bound@%n_0))
(rule (let ((a!1 (=> linger_dec_bound@_call_0
               (= linger_dec_bound@%_14_0 (not (= linger_dec_bound@%_13_0 0))))))
(let ((a!2 (and (linger_dec_bound@_1
                  linger_dec_bound@%_tail_0
                  linger_dec_bound@%pa_0
                  @nd_0
                  linger_dec_bound@%n_0)
                true
                (> linger_dec_bound@%x_0 0)
                (= linger_dec_bound@%_br_0 (= linger_dec_bound@%n_0 0))
                (=> linger_dec_bound@_call_0
                    (and linger_dec_bound@_call_0 linger_dec_bound@_1_0))
                (=> (and linger_dec_bound@_call_0 linger_dec_bound@_1_0)
                    (not linger_dec_bound@%_br_0))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_5_0
                       (select linger_dec_bound@%_tail_0 linger_dec_bound@%pa_0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_6_0 (+ linger_dec_bound@%_5_0 (- 1))))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_store_0
                       (store linger_dec_bound@%_tail_0
                              linger_dec_bound@%pa_0
                              linger_dec_bound@%_6_0)))
                (=> linger_dec_bound@_call_0 (= linger_dec_bound@%_8_0 @nd_0))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_store1_0
                       (store linger_dec_bound@%_store_0
                              linger_dec_bound@%x_0
                              linger_dec_bound@%_9_0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_11_0 (+ linger_dec_bound@%n_0 (- 1))))
                (=> linger_dec_bound@_call_0 (= linger_dec_bound@%_12_0 @nd_0))
                a!1
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_15_0
                       (ite linger_dec_bound@%_14_0
                            linger_dec_bound@%x_0
                            linger_dec_bound@%pa_0)))
                (linger_dec_bound linger_dec_bound@_call_0
                                  false
                                  false
                                  linger_dec_bound@%_store1_0
                                  linger_dec_bound@%_call2_0
                                  linger_dec_bound@%_11_0
                                  linger_dec_bound@%_15_0)
                (=> |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)|
                    linger_dec_bound@_1_0)
                (=> linger_dec_bound@_shadow.mem.0_0
                    (or (and linger_dec_bound@_shadow.mem.0_0
                             linger_dec_bound@_call_0)
                        (and linger_dec_bound@_1_0
                             |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)|)))
                linger_dec_bound@_shadow.mem.0_0
                (=> (and linger_dec_bound@_shadow.mem.0_0
                         linger_dec_bound@_call_0)
                    (= linger_dec_bound@%shadow.mem.0_0
                       linger_dec_bound@%_call2_0))
                (=> (and linger_dec_bound@_1_0
                         |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)|)
                    linger_dec_bound@%_br_0)
                (=> (and linger_dec_bound@_1_0
                         |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)|)
                    (= linger_dec_bound@%shadow.mem.0_1
                       linger_dec_bound@%_tail_0))
                (=> (and linger_dec_bound@_shadow.mem.0_0
                         linger_dec_bound@_call_0)
                    (= linger_dec_bound@%shadow.mem.0_2
                       linger_dec_bound@%shadow.mem.0_0))
                (=> (and linger_dec_bound@_1_0
                         |tuple(linger_dec_bound@_1_0, linger_dec_bound@_shadow.mem.0_0)|)
                    (= linger_dec_bound@%shadow.mem.0_2
                       linger_dec_bound@%shadow.mem.0_1)))))
  (=> a!2
      (linger_dec_bound@_shadow.mem.0
        linger_dec_bound@%_tail_0
        linger_dec_bound@%shadow.mem.0_2
        linger_dec_bound@%pa_0
        @nd_0
        linger_dec_bound@%n_0)))))
(rule (=> (linger_dec_bound@_shadow.mem.0
      linger_dec_bound@%_tail_0
      linger_dec_bound@%shadow.mem.0_0
      linger_dec_bound@%pa_0
      @nd_0
      linger_dec_bound@%n_0)
    (linger_dec_bound true
                      false
                      false
                      linger_dec_bound@%_tail_0
                      linger_dec_bound@%shadow.mem.0_0
                      linger_dec_bound@%n_0
                      linger_dec_bound@%pa_0)))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%a.i_0 0)
                (= main@%_1_0 @nd_0)
                (= main@%_3_0 @nd_0)
                (= main@%_5_0 (store main@%_0_0 main@%a.i_0 main@%_4_0))
                (linger_dec_bound true
                                  false
                                  false
                                  main@%_5_0
                                  main@%_6_0
                                  main@%_2_0
                                  main@%a.i_0)
                (= main@%_7_0 (select main@%_6_0 main@%a.i_0))
                (= main@%_8_0 (< main@%_4_0 main@%_7_0))
                (=> main@_bb_0 (and main@_bb_0 main@entry_0))
                (=> (and main@_bb_0 main@entry_0) (not main@%_8_0))
                (=> main@_bb_0 (= main@%_10_0 (- main@%_4_0 main@%_7_0)))
                (=> main@_bb_0 (= main@%_11_0 (> main@%_10_0 main@%_2_0)))
                (=> main@_bb_0 main@%_11_0)
                (=> |tuple(main@entry_0, main@verifier.error_0)| main@entry_0)
                (=> main@verifier.error_0
                    (or (and main@entry_0
                             |tuple(main@entry_0, main@verifier.error_0)|)
                        (and main@verifier.error_0 main@_bb_0)))
                (=> (and main@entry_0
                         |tuple(main@entry_0, main@verifier.error_0)|)
                    main@%_8_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

