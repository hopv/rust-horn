(set-info :original "08-linger-dec/linger-dec-2-basic3-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel linger_dec_three@_sm4 ((Array Int Int) Int Int Int Int ))
(declare-rel linger_dec_three@_shadow.mem.0.0 ((Array Int Int) (Array Int Int) Int Int Int Int ))
(declare-rel linger_dec_three (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@entry.split ())
(declare-var linger_dec_three@%_27_0 Int )
(declare-var linger_dec_three@%_28_0 Int )
(declare-var linger_dec_three@%_spec.select_0 Bool )
(declare-var linger_dec_three@%_23_0 Int )
(declare-var linger_dec_three@%_24_0 Int )
(declare-var linger_dec_three@%_br7_0 Bool )
(declare-var linger_dec_three@%_call5_0 Int )
(declare-var linger_dec_three@%_17_0 Int )
(declare-var linger_dec_three@%_sm3_0 Int )
(declare-var linger_dec_three@%_19_0 Int )
(declare-var linger_dec_three@%_20_0 Int )
(declare-var linger_dec_three@%_br6_0 Bool )
(declare-var linger_dec_three@%.02_2 Int )
(declare-var linger_dec_three@%.01_2 Int )
(declare-var linger_dec_three@%.0_2 Int )
(declare-var linger_dec_three@%_6_0 Int )
(declare-var linger_dec_three@%_sm_0 Int )
(declare-var linger_dec_three@%sm_0 (Array Int Int) )
(declare-var linger_dec_three@%_8_0 Int )
(declare-var linger_dec_three@%_sm1_0 Int )
(declare-var linger_dec_three@%sm1_0 (Array Int Int) )
(declare-var linger_dec_three@%_10_0 Int )
(declare-var linger_dec_three@%_sm2_0 Int )
(declare-var linger_dec_three@%_12_0 Int )
(declare-var linger_dec_three@%_13_0 Int )
(declare-var linger_dec_three@%_br_0 Bool )
(declare-var linger_dec_three@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var linger_dec_three@%sm4_0 (Array Int Int) )
(declare-var linger_dec_three@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var linger_dec_three@arg.0_0 Int )
(declare-var linger_dec_three@arg.1_0 Int )
(declare-var linger_dec_three@arg.2_0 Int )
(declare-var @nd_0 Int )
(declare-var linger_dec_three@_sm4_0 Bool )
(declare-var linger_dec_three@%_call_0 Int )
(declare-var linger_dec_three@%sm2_0 (Array Int Int) )
(declare-var linger_dec_three@_15_0 Bool )
(declare-var linger_dec_three@%sm3_0 (Array Int Int) )
(declare-var linger_dec_three@_22_0 Bool )
(declare-var linger_dec_three@_26_0 Bool )
(declare-var linger_dec_three@%spec.select_0 Int )
(declare-var linger_dec_three@_.02_0 Bool )
(declare-var |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)| Bool )
(declare-var |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)| Bool )
(declare-var linger_dec_three@%.02_0 Int )
(declare-var linger_dec_three@%.01_0 Int )
(declare-var linger_dec_three@%.0_0 Int )
(declare-var linger_dec_three@%.02_1 Int )
(declare-var linger_dec_three@%.01_1 Int )
(declare-var linger_dec_three@%.0_1 Int )
(declare-var linger_dec_three@%.02_3 Int )
(declare-var linger_dec_three@%.01_3 Int )
(declare-var linger_dec_three@%.0_3 Int )
(declare-var linger_dec_three@%sh_0 (Array Int Int) )
(declare-var linger_dec_three@_shadow.mem.0.0_0 Bool )
(declare-var |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)| Bool )
(declare-var linger_dec_three@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@entry.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (linger_dec_three true
                  true
                  true
                  linger_dec_three@%sm4_0
                  linger_dec_three@%shadow.mem.0.0_0
                  linger_dec_three@arg.0_0
                  linger_dec_three@arg.1_0
                  linger_dec_three@arg.2_0))
(rule (linger_dec_three false
                  true
                  true
                  linger_dec_three@%sm4_0
                  linger_dec_three@%shadow.mem.0.0_0
                  linger_dec_three@arg.0_0
                  linger_dec_three@arg.1_0
                  linger_dec_three@arg.2_0))
(rule (linger_dec_three false
                  false
                  false
                  linger_dec_three@%sm4_0
                  linger_dec_three@%shadow.mem.0.0_0
                  linger_dec_three@arg.0_0
                  linger_dec_three@arg.1_0
                  linger_dec_three@arg.2_0))
(rule (linger_dec_three@_sm4
  linger_dec_three@%sm4_0
  @nd_0
  linger_dec_three@arg.2_0
  linger_dec_three@arg.1_0
  linger_dec_three@arg.0_0))
(rule (let ((a!1 (and (linger_dec_three@_sm4
                  linger_dec_three@%sm4_0
                  @nd_0
                  linger_dec_three@arg.2_0
                  linger_dec_three@arg.1_0
                  linger_dec_three@arg.0_0)
                true
                (> linger_dec_three@%_call_0 0)
                (= linger_dec_three@%_6_0
                   (select linger_dec_three@%sm4_0 linger_dec_three@arg.0_0))
                (= linger_dec_three@%_sm_0 (+ linger_dec_three@%_6_0 (- 1)))
                (= linger_dec_three@%sm_0
                   (store linger_dec_three@%sm4_0
                          linger_dec_three@arg.0_0
                          linger_dec_three@%_sm_0))
                (= linger_dec_three@%_8_0
                   (select linger_dec_three@%sm4_0 linger_dec_three@arg.1_0))
                (= linger_dec_three@%_sm1_0 (+ linger_dec_three@%_8_0 (- 2)))
                (= linger_dec_three@%sm1_0
                   (store linger_dec_three@%sm_0
                          linger_dec_three@arg.1_0
                          linger_dec_three@%_sm1_0))
                (= linger_dec_three@%_10_0
                   (select linger_dec_three@%sm4_0 linger_dec_three@arg.2_0))
                (= linger_dec_three@%_sm2_0 (+ linger_dec_three@%_10_0 (- 3)))
                (= linger_dec_three@%sm2_0
                   (store linger_dec_three@%sm1_0
                          linger_dec_three@arg.2_0
                          linger_dec_three@%_sm2_0))
                (= linger_dec_three@%_12_0 @nd_0)
                (= linger_dec_three@%_br_0 (= linger_dec_three@%_13_0 0))
                (=> linger_dec_three@_15_0
                    (and linger_dec_three@_15_0 linger_dec_three@_sm4_0))
                (=> (and linger_dec_three@_15_0 linger_dec_three@_sm4_0)
                    linger_dec_three@%_br_0)
                (=> linger_dec_three@_15_0
                    (= linger_dec_three@%_call5_0 linger_dec_three@%_call_0))
                (=> linger_dec_three@_15_0 (= linger_dec_three@%_17_0 @nd_0))
                (=> linger_dec_three@_15_0
                    (= linger_dec_three@%sm3_0
                       (store linger_dec_three@%sm2_0
                              linger_dec_three@%_call_0
                              linger_dec_three@%_sm3_0)))
                (=> linger_dec_three@_15_0 (= linger_dec_three@%_19_0 @nd_0))
                (=> linger_dec_three@_15_0
                    (= linger_dec_three@%_br6_0 (= linger_dec_three@%_20_0 0)))
                (=> linger_dec_three@_22_0
                    (and linger_dec_three@_22_0 linger_dec_three@_15_0))
                (=> (and linger_dec_three@_22_0 linger_dec_three@_15_0)
                    linger_dec_three@%_br6_0)
                (=> linger_dec_three@_22_0 (= linger_dec_three@%_23_0 @nd_0))
                (=> linger_dec_three@_22_0
                    (= linger_dec_three@%_br7_0 (= linger_dec_three@%_24_0 0)))
                (=> linger_dec_three@_26_0
                    (and linger_dec_three@_26_0 linger_dec_three@_22_0))
                (=> (and linger_dec_three@_26_0 linger_dec_three@_22_0)
                    linger_dec_three@%_br7_0)
                (=> linger_dec_three@_26_0 (= linger_dec_three@%_27_0 @nd_0))
                (=> linger_dec_three@_26_0
                    (= linger_dec_three@%_spec.select_0
                       (= linger_dec_three@%_28_0 0)))
                (=> linger_dec_three@_26_0
                    (= linger_dec_three@%spec.select_0
                       (ite linger_dec_three@%_spec.select_0
                            linger_dec_three@arg.2_0
                            linger_dec_three@%_call_0)))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    linger_dec_three@_22_0)
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    linger_dec_three@_15_0)
                (=> linger_dec_three@_.02_0
                    (or (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                        |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                        |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (not linger_dec_three@%_br7_0))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (not linger_dec_three@%_br6_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.02_0 linger_dec_three@%spec.select_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.01_0 linger_dec_three@arg.1_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.0_0 linger_dec_three@arg.0_0))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.02_1 linger_dec_three@arg.2_0))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.01_1 linger_dec_three@%_call_0))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.0_1 linger_dec_three@arg.0_0))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.02_2 linger_dec_three@arg.2_0))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.01_2 linger_dec_three@arg.1_0))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.0_2 linger_dec_three@%_call_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.02_3 linger_dec_three@%.02_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.01_3 linger_dec_three@%.01_0))
                (=> (and linger_dec_three@_.02_0 linger_dec_three@_26_0)
                    (= linger_dec_three@%.0_3 linger_dec_three@%.0_0))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.02_3 linger_dec_three@%.02_1))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.01_3 linger_dec_three@%.01_1))
                (=> |tuple(linger_dec_three@_22_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.0_3 linger_dec_three@%.0_1))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.02_3 linger_dec_three@%.02_2))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.01_3 linger_dec_three@%.01_2))
                (=> |tuple(linger_dec_three@_15_0, linger_dec_three@_.02_0)|
                    (= linger_dec_three@%.0_3 linger_dec_three@%.0_2))
                (linger_dec_three linger_dec_three@_.02_0
                                  false
                                  false
                                  linger_dec_three@%sm3_0
                                  linger_dec_three@%sh_0
                                  linger_dec_three@%.0_3
                                  linger_dec_three@%.01_3
                                  linger_dec_three@%.02_3)
                (=> |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)|
                    linger_dec_three@_sm4_0)
                (=> linger_dec_three@_shadow.mem.0.0_0
                    (or (and linger_dec_three@_shadow.mem.0.0_0
                             linger_dec_three@_.02_0)
                        |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)|))
                (=> |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)|
                    (not linger_dec_three@%_br_0))
                (=> (and linger_dec_three@_shadow.mem.0.0_0
                         linger_dec_three@_.02_0)
                    (= linger_dec_three@%shadow.mem.0.0_0
                       linger_dec_three@%sh_0))
                (=> |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)|
                    (= linger_dec_three@%shadow.mem.0.0_1
                       linger_dec_three@%sm2_0))
                (=> (and linger_dec_three@_shadow.mem.0.0_0
                         linger_dec_three@_.02_0)
                    (= linger_dec_three@%shadow.mem.0.0_2
                       linger_dec_three@%shadow.mem.0.0_0))
                (=> |tuple(linger_dec_three@_sm4_0, linger_dec_three@_shadow.mem.0.0_0)|
                    (= linger_dec_three@%shadow.mem.0.0_2
                       linger_dec_three@%shadow.mem.0.0_1))
                linger_dec_three@_shadow.mem.0.0_0)))
  (=> a!1
      (linger_dec_three@_shadow.mem.0.0
        linger_dec_three@%sm4_0
        linger_dec_three@%shadow.mem.0.0_2
        @nd_0
        linger_dec_three@arg.2_0
        linger_dec_three@arg.1_0
        linger_dec_three@arg.0_0))))
(rule (=> (linger_dec_three@_shadow.mem.0.0
      linger_dec_three@%sm4_0
      linger_dec_three@%shadow.mem.0.0_0
      @nd_0
      linger_dec_three@arg.2_0
      linger_dec_three@arg.1_0
      linger_dec_three@arg.0_0)
    (linger_dec_three true
                      false
                      false
                      linger_dec_three@%sm4_0
                      linger_dec_three@%shadow.mem.0.0_0
                      linger_dec_three@arg.0_0
                      linger_dec_three@arg.1_0
                      linger_dec_three@arg.2_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (> main@%_0_0 0)
         (> main@%_1_0 0)
         (> main@%_2_0 0)
         (= main@%_3_0 main@%_0_0)
         (= main@%_4_0 @nd_0)
         (= main@%sm_0 (store main@%sm3_0 main@%_0_0 main@%_5_0))
         (= main@%_6_0 main@%_1_0)
         (= main@%_7_0 @nd_0)
         (= main@%sm1_0 (store main@%sm_0 main@%_1_0 main@%_8_0))
         (= main@%_9_0 main@%_2_0)
         (= main@%_10_0 @nd_0)
         (= main@%sm2_0 (store main@%sm1_0 main@%_2_0 main@%_11_0))
         (linger_dec_three true
                           false
                           false
                           main@%sm2_0
                           main@%sh_0
                           main@%_0_0
                           main@%_1_0
                           main@%_2_0)
         (= main@%_12_0 (select main@%sh_0 main@%_0_0))
         (= main@%_13_0 (> main@%_5_0 main@%_12_0))
         (not main@%_13_0)
         (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
         main@entry.split_0)
    main@entry.split))
(query main@entry.split)

