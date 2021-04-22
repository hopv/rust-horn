(set-info :original "08-linger-dec/linger-dec-1-basic-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel linger_dec@_sm2 ((Array Int Int) Int Int ))
(declare-rel linger_dec@_shadow.mem.0.0 ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel linger_dec (Bool Bool Bool (Array Int Int) (Array Int Int) Int ))
(declare-rel main@entry (Int ))
(declare-rel main@entry.split ())
(declare-var linger_dec@%_call3_0 Int )
(declare-var linger_dec@%_11_0 Int )
(declare-var linger_dec@%_sm1_0 Int )
(declare-var linger_dec@%sm1_0 (Array Int Int) )
(declare-var linger_dec@%_13_0 Int )
(declare-var linger_dec@%_14_0 Int )
(declare-var linger_dec@%_15_0 Bool )
(declare-var linger_dec@%_sh_0 Int )
(declare-var linger_dec@%_4_0 Int )
(declare-var linger_dec@%_sm_0 Int )
(declare-var linger_dec@%_6_0 Int )
(declare-var linger_dec@%_7_0 Int )
(declare-var linger_dec@%_br_0 Bool )
(declare-var linger_dec@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var linger_dec@%sm2_0 (Array Int Int) )
(declare-var linger_dec@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var linger_dec@arg.0_0 Int )
(declare-var @nd_0 Int )
(declare-var linger_dec@_sm2_0 Bool )
(declare-var linger_dec@%_call_0 Int )
(declare-var linger_dec@%sm_0 (Array Int Int) )
(declare-var linger_dec@_9_0 Bool )
(declare-var linger_dec@%sh_0 (Array Int Int) )
(declare-var linger_dec@_shadow.mem.0.0_0 Bool )
(declare-var |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)| Bool )
(declare-var linger_dec@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@entry.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (linger_dec true
            true
            true
            linger_dec@%sm2_0
            linger_dec@%shadow.mem.0.0_0
            linger_dec@arg.0_0))
(rule (linger_dec false
            true
            true
            linger_dec@%sm2_0
            linger_dec@%shadow.mem.0.0_0
            linger_dec@arg.0_0))
(rule (linger_dec false
            false
            false
            linger_dec@%sm2_0
            linger_dec@%shadow.mem.0.0_0
            linger_dec@arg.0_0))
(rule (linger_dec@_sm2 linger_dec@%sm2_0 @nd_0 linger_dec@arg.0_0))
(rule (let ((a!1 (and (linger_dec@_sm2 linger_dec@%sm2_0 @nd_0 linger_dec@arg.0_0)
                true
                (> linger_dec@%_call_0 0)
                (= linger_dec@%_4_0
                   (select linger_dec@%sm2_0 linger_dec@arg.0_0))
                (= linger_dec@%_sm_0 (+ linger_dec@%_4_0 (- 1)))
                (= linger_dec@%sm_0
                   (store linger_dec@%sm2_0
                          linger_dec@arg.0_0
                          linger_dec@%_sm_0))
                (= linger_dec@%_6_0 @nd_0)
                (= linger_dec@%_br_0 (= linger_dec@%_7_0 0))
                (=> linger_dec@_9_0 (and linger_dec@_9_0 linger_dec@_sm2_0))
                (=> (and linger_dec@_9_0 linger_dec@_sm2_0) linger_dec@%_br_0)
                (=> linger_dec@_9_0
                    (= linger_dec@%_call3_0 linger_dec@%_call_0))
                (=> linger_dec@_9_0 (= linger_dec@%_11_0 @nd_0))
                (=> linger_dec@_9_0
                    (= linger_dec@%sm1_0
                       (store linger_dec@%sm_0
                              linger_dec@%_call_0
                              linger_dec@%_sm1_0)))
                (=> linger_dec@_9_0 (= linger_dec@%_13_0 @nd_0))
                (=> linger_dec@_9_0
                    (= linger_dec@%_15_0 (= linger_dec@%_14_0 0)))
                (=> linger_dec@_9_0
                    (= linger_dec@%_sh_0
                       (ite linger_dec@%_15_0
                            linger_dec@arg.0_0
                            linger_dec@%_call_0)))
                (linger_dec linger_dec@_9_0
                            false
                            false
                            linger_dec@%sm1_0
                            linger_dec@%sh_0
                            linger_dec@%_sh_0)
                (=> |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)|
                    linger_dec@_sm2_0)
                (=> linger_dec@_shadow.mem.0.0_0
                    (or (and linger_dec@_shadow.mem.0.0_0 linger_dec@_9_0)
                        |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)|))
                (=> |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)|
                    (not linger_dec@%_br_0))
                (=> (and linger_dec@_shadow.mem.0.0_0 linger_dec@_9_0)
                    (= linger_dec@%shadow.mem.0.0_0 linger_dec@%sh_0))
                (=> |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)|
                    (= linger_dec@%shadow.mem.0.0_1 linger_dec@%sm_0))
                (=> (and linger_dec@_shadow.mem.0.0_0 linger_dec@_9_0)
                    (= linger_dec@%shadow.mem.0.0_2
                       linger_dec@%shadow.mem.0.0_0))
                (=> |tuple(linger_dec@_sm2_0, linger_dec@_shadow.mem.0.0_0)|
                    (= linger_dec@%shadow.mem.0.0_2
                       linger_dec@%shadow.mem.0.0_1))
                linger_dec@_shadow.mem.0.0_0)))
  (=> a!1
      (linger_dec@_shadow.mem.0.0
        linger_dec@%sm2_0
        linger_dec@%shadow.mem.0.0_2
        @nd_0
        linger_dec@arg.0_0))))
(rule (=> (linger_dec@_shadow.mem.0.0
      linger_dec@%sm2_0
      linger_dec@%shadow.mem.0.0_0
      @nd_0
      linger_dec@arg.0_0)
    (linger_dec true
                false
                false
                linger_dec@%sm2_0
                linger_dec@%shadow.mem.0.0_0
                linger_dec@arg.0_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (> main@%_0_0 0)
         (= main@%_1_0 main@%_0_0)
         (= main@%_2_0 @nd_0)
         (= main@%sm_0 (store main@%sm1_0 main@%_0_0 main@%_3_0))
         (linger_dec true false false main@%sm_0 main@%sh_0 main@%_0_0)
         (= main@%_4_0 (select main@%sh_0 main@%_0_0))
         (= main@%_5_0 (> main@%_3_0 main@%_4_0))
         (not main@%_5_0)
         (=> main@entry.split_0 (and main@entry.split_0 main@entry_0))
         main@entry.split_0)
    main@entry.split))
(query main@entry.split)

