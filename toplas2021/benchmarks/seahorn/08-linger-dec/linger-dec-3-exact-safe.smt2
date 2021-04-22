(set-info :original "08-linger-dec/linger-dec-3-exact-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel linger_dec_bound@_sm2 ((Array Int Int) Int Int Int ))
(declare-rel linger_dec_bound@_shadow.mem.0.0 ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel linger_dec_bound (Bool Bool Bool (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@entry (Int ))
(declare-rel main@verifier.error.split ())
(declare-var linger_dec_bound@%_7_0 Int )
(declare-var linger_dec_bound@arg.1_0 Int )
(declare-var linger_dec_bound@%_sm_0 Int )
(declare-var linger_dec_bound@%sm_0 (Array Int Int) )
(declare-var linger_dec_bound@%_call3_0 Int )
(declare-var linger_dec_bound@%_10_0 Int )
(declare-var @nd_0 Int )
(declare-var linger_dec_bound@%_sm1_0 Int )
(declare-var linger_dec_bound@%sm1_0 (Array Int Int) )
(declare-var linger_dec_bound@%_12_0 Int )
(declare-var linger_dec_bound@%_13_0 Int )
(declare-var linger_dec_bound@%_14_0 Int )
(declare-var linger_dec_bound@%_15_0 Bool )
(declare-var linger_dec_bound@%_sh_0 Int )
(declare-var linger_dec_bound@%_br_0 Bool )
(declare-var linger_dec_bound@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var linger_dec_bound@%sm2_0 (Array Int Int) )
(declare-var linger_dec_bound@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var linger_dec_bound@arg.0_0 Int )
(declare-var linger_dec_bound@_sm2_0 Bool )
(declare-var linger_dec_bound@%_4_0 Int )
(declare-var linger_dec_bound@_call_0 Bool )
(declare-var linger_dec_bound@%sh_0 (Array Int Int) )
(declare-var linger_dec_bound@_shadow.mem.0.0_0 Bool )
(declare-var |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)| Bool )
(declare-var linger_dec_bound@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_7_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@_8_0 Bool )
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
                  linger_dec_bound@%sm2_0
                  linger_dec_bound@%shadow.mem.0.0_0
                  linger_dec_bound@arg.0_0
                  linger_dec_bound@arg.1_0))
(rule (linger_dec_bound false
                  true
                  true
                  linger_dec_bound@%sm2_0
                  linger_dec_bound@%shadow.mem.0.0_0
                  linger_dec_bound@arg.0_0
                  linger_dec_bound@arg.1_0))
(rule (linger_dec_bound false
                  false
                  false
                  linger_dec_bound@%sm2_0
                  linger_dec_bound@%shadow.mem.0.0_0
                  linger_dec_bound@arg.0_0
                  linger_dec_bound@arg.1_0))
(rule (linger_dec_bound@_sm2
  linger_dec_bound@%sm2_0
  linger_dec_bound@arg.1_0
  @nd_0
  linger_dec_bound@arg.0_0))
(rule (let ((a!1 (and (linger_dec_bound@_sm2
                  linger_dec_bound@%sm2_0
                  linger_dec_bound@arg.1_0
                  @nd_0
                  linger_dec_bound@arg.0_0)
                true
                (> linger_dec_bound@%_4_0 0)
                (= linger_dec_bound@%_br_0 (= linger_dec_bound@arg.0_0 0))
                (=> linger_dec_bound@_call_0
                    (and linger_dec_bound@_call_0 linger_dec_bound@_sm2_0))
                (=> (and linger_dec_bound@_call_0 linger_dec_bound@_sm2_0)
                    (not linger_dec_bound@%_br_0))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_7_0
                       (select linger_dec_bound@%sm2_0 linger_dec_bound@arg.1_0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_sm_0 (+ linger_dec_bound@%_7_0 (- 1))))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%sm_0
                       (store linger_dec_bound@%sm2_0
                              linger_dec_bound@arg.1_0
                              linger_dec_bound@%_sm_0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_call3_0 linger_dec_bound@%_4_0))
                (=> linger_dec_bound@_call_0 (= linger_dec_bound@%_10_0 @nd_0))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%sm1_0
                       (store linger_dec_bound@%sm_0
                              linger_dec_bound@%_4_0
                              linger_dec_bound@%_sm1_0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_12_0
                       (+ linger_dec_bound@arg.0_0 (- 1))))
                (=> linger_dec_bound@_call_0 (= linger_dec_bound@%_13_0 @nd_0))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_15_0 (= linger_dec_bound@%_14_0 0)))
                (=> linger_dec_bound@_call_0
                    (= linger_dec_bound@%_sh_0
                       (ite linger_dec_bound@%_15_0
                            linger_dec_bound@arg.1_0
                            linger_dec_bound@%_4_0)))
                (linger_dec_bound linger_dec_bound@_call_0
                                  false
                                  false
                                  linger_dec_bound@%sm1_0
                                  linger_dec_bound@%sh_0
                                  linger_dec_bound@%_12_0
                                  linger_dec_bound@%_sh_0)
                (=> |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)|
                    linger_dec_bound@_sm2_0)
                (=> linger_dec_bound@_shadow.mem.0.0_0
                    (or (and linger_dec_bound@_shadow.mem.0.0_0
                             linger_dec_bound@_call_0)
                        |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)|))
                (=> |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)|
                    linger_dec_bound@%_br_0)
                (=> (and linger_dec_bound@_shadow.mem.0.0_0
                         linger_dec_bound@_call_0)
                    (= linger_dec_bound@%shadow.mem.0.0_0
                       linger_dec_bound@%sh_0))
                (=> |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)|
                    (= linger_dec_bound@%shadow.mem.0.0_1
                       linger_dec_bound@%sm2_0))
                (=> (and linger_dec_bound@_shadow.mem.0.0_0
                         linger_dec_bound@_call_0)
                    (= linger_dec_bound@%shadow.mem.0.0_2
                       linger_dec_bound@%shadow.mem.0.0_0))
                (=> |tuple(linger_dec_bound@_sm2_0, linger_dec_bound@_shadow.mem.0.0_0)|
                    (= linger_dec_bound@%shadow.mem.0.0_2
                       linger_dec_bound@%shadow.mem.0.0_1))
                linger_dec_bound@_shadow.mem.0.0_0)))
  (=> a!1
      (linger_dec_bound@_shadow.mem.0.0
        linger_dec_bound@%sm2_0
        linger_dec_bound@%shadow.mem.0.0_2
        linger_dec_bound@arg.1_0
        @nd_0
        linger_dec_bound@arg.0_0))))
(rule (=> (linger_dec_bound@_shadow.mem.0.0
      linger_dec_bound@%sm2_0
      linger_dec_bound@%shadow.mem.0.0_0
      linger_dec_bound@arg.1_0
      @nd_0
      linger_dec_bound@arg.0_0)
    (linger_dec_bound true
                      false
                      false
                      linger_dec_bound@%sm2_0
                      linger_dec_bound@%shadow.mem.0.0_0
                      linger_dec_bound@arg.0_0
                      linger_dec_bound@arg.1_0)))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%_0_0 0)
                (= main@%_1_0 @nd_0)
                (= main@%_3_0 main@%_0_0)
                (= main@%_4_0 @nd_0)
                (= main@%sm_0 (store main@%sm1_0 main@%_0_0 main@%_5_0))
                (linger_dec_bound true
                                  false
                                  false
                                  main@%sm_0
                                  main@%sh_0
                                  main@%_2_0
                                  main@%_0_0)
                (= main@%_6_0 (select main@%sh_0 main@%_0_0))
                (= main@%_7_0 (< main@%_5_0 main@%_6_0))
                (=> main@_8_0 (and main@_8_0 main@entry_0))
                (=> (and main@_8_0 main@entry_0) (not main@%_7_0))
                (=> main@_8_0 (= main@%_9_0 (- main@%_5_0 main@%_6_0)))
                (=> main@_8_0 (= main@%_10_0 (> main@%_9_0 main@%_2_0)))
                (=> main@_8_0 main@%_10_0)
                (=> |tuple(main@entry_0, main@verifier.error_0)| main@entry_0)
                (=> main@verifier.error_0
                    (or |tuple(main@entry_0, main@verifier.error_0)|
                        (and main@verifier.error_0 main@_8_0)))
                (=> |tuple(main@entry_0, main@verifier.error_0)| main@%_7_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

