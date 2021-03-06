(set-info :original "05-swap-dec/swap-dec-1-base-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int Int (Array Int Int) Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%_23_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%spec.select1014_2 Int )
(declare-var main@%spec.select13_2 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%.0.sroa_cast_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%.0.sroa_cast9_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var @nd_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_9_0 Bool )
(declare-var main@tailrecurse.i.preheader_0 Bool )
(declare-var main@%spec.select1012_0 Int )
(declare-var main@%spec.select11_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%spec.select1014_0 Int )
(declare-var main@%spec.select13_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%spec.select1014_1 Int )
(declare-var main@%spec.select13_1 Int )
(declare-var main@swap_dec.exit.thread_0 Bool )
(declare-var main@%.0.817_0 Int )
(declare-var main@%.0.817_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select10_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@swap_dec.exit_0 Bool )
(declare-var main@%.0.8.pre_0 Int )
(declare-var |tuple(main@swap_dec.exit_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (distinct main@%_1_0 main@%_2_0) ; added
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_3_0 @nd_0)
                (= main@%sm_0 (store main@%sm4_0 main@%_1_0 main@%_4_0))
                (= main@%.0.sroa_cast9_0 main@%_2_0)
                (= main@%_5_0 @nd_0)
                (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_6_0))
                (= main@%_7_0 @nd_0)
                (= main@%_9_0 (= main@%_8_0 0))
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@tailrecurse.i.preheader_0
                    (and main@tailrecurse.i.preheader_0 main@entry_0))
                (=> (and main@tailrecurse.i.preheader_0 main@entry_0)
                    main@%_12_0)
                (=> main@tailrecurse.i.preheader_0
                    (= main@%spec.select1012_0
                       (ite main@%_9_0 main@%_2_0 main@%_1_0)))
                (=> main@tailrecurse.i.preheader_0
                    (= main@%spec.select11_0
                       (ite main@%_9_0 main@%_1_0 main@%_2_0)))
                (=> main@tailrecurse.i_0
                    (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%shadow.mem.0.0_0 main@%sm1_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select1014_0 main@%spec.select1012_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select13_0 main@%spec.select11_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select1014_1 main@%spec.select1014_0))
                (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
                    (= main@%spec.select13_1 main@%spec.select13_0))
                main@tailrecurse.i_0)))
  (=> a!1
      (main@tailrecurse.i
        main@%_4_0
        main@%_1_0
        main@%shadow.mem.0.0_1
        main@%spec.select13_1
        main@%spec.select1014_1
        @nd_0
        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (> main@%_1_0 0)
                (> main@%_2_0 0)
                (distinct main@%_1_0 main@%_2_0) ; added
                (= main@%.0.sroa_cast_0 main@%_1_0)
                (= main@%_3_0 @nd_0)
                (= main@%sm_0 (store main@%sm4_0 main@%_1_0 main@%_4_0))
                (= main@%.0.sroa_cast9_0 main@%_2_0)
                (= main@%_5_0 @nd_0)
                (= main@%sm1_0 (store main@%sm_0 main@%_2_0 main@%_6_0))
                (= main@%_7_0 @nd_0)
                (= main@%_9_0 (= main@%_8_0 0))
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@swap_dec.exit.thread_0
                    (and main@swap_dec.exit.thread_0 main@entry_0))
                (=> (and main@swap_dec.exit.thread_0 main@entry_0)
                    (not main@%_12_0))
                (=> (and main@swap_dec.exit.thread_0 main@entry_0)
                    (= main@%.0.817_0 main@%_4_0))
                (=> (and main@swap_dec.exit.thread_0 main@entry_0)
                    (= main@%.0.817_1 main@%.0.817_0))
                (=> main@swap_dec.exit.thread_0
                    (= main@%_24_0 (- main@%_4_0 main@%.0.817_1)))
                (=> main@swap_dec.exit.thread_0
                    (= main@%_25_0 (< main@%_24_0 4)))
                (=> main@swap_dec.exit.thread_0 (not main@%_25_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@swap_dec.exit.thread_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@tailrecurse.i
           main@%_4_0
           main@%_1_0
           main@%shadow.mem.0.0_0
           main@%spec.select13_0
           main@%spec.select1014_0
           @nd_0
           main@%loop.bound_0)
         true
         (= main@%_13_0 (select main@%shadow.mem.0.0_0 main@%spec.select13_0))
         (= main@%_14_0 (+ main@%_13_0 (- 1)))
         (= main@%sm2_0
            (store main@%shadow.mem.0.0_0 main@%spec.select13_0 main@%_14_0))
         (= main@%_15_0 (select main@%sm2_0 main@%spec.select1014_0))
         (= main@%_16_0 (+ main@%_15_0 (- 2)))
         (= main@%sm3_0 (store main@%sm2_0 main@%spec.select1014_0 main@%_16_0))
         (= main@%_17_0 @nd_0)
         (= main@%_19_0 (= main@%_18_0 0))
         (= main@%spec.select_0
            (ite main@%_19_0 main@%spec.select13_0 main@%spec.select1014_0))
         (= main@%spec.select10_0
            (ite main@%_19_0 main@%spec.select1014_0 main@%spec.select13_0))
         (= main@%_20_0 @nd_0)
         (= main@%_22_0 (= main@%_21_0 main@%loop.bound_0))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) main@%_22_0)
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_1 main@%sm3_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select1014_1 main@%spec.select10_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select13_1 main@%spec.select_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select1014_2 main@%spec.select1014_1))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%spec.select13_2 main@%spec.select13_1))
         main@tailrecurse.i_1)
    (main@tailrecurse.i
      main@%_4_0
      main@%_1_0
      main@%shadow.mem.0.0_2
      main@%spec.select13_2
      main@%spec.select1014_2
      @nd_0
      main@%loop.bound_0)))
(rule (let ((a!1 (and (main@tailrecurse.i
                  main@%_4_0
                  main@%_1_0
                  main@%shadow.mem.0.0_0
                  main@%spec.select13_0
                  main@%spec.select1014_0
                  @nd_0
                  main@%loop.bound_0)
                true
                (= main@%_13_0
                   (select main@%shadow.mem.0.0_0 main@%spec.select13_0))
                (= main@%_14_0 (+ main@%_13_0 (- 1)))
                (= main@%sm2_0
                   (store main@%shadow.mem.0.0_0
                          main@%spec.select13_0
                          main@%_14_0))
                (= main@%_15_0 (select main@%sm2_0 main@%spec.select1014_0))
                (= main@%_16_0 (+ main@%_15_0 (- 2)))
                (= main@%sm3_0
                   (store main@%sm2_0 main@%spec.select1014_0 main@%_16_0))
                (= main@%_17_0 @nd_0)
                (= main@%_19_0 (= main@%_18_0 0))
                (= main@%spec.select_0
                   (ite main@%_19_0
                        main@%spec.select13_0
                        main@%spec.select1014_0))
                (= main@%spec.select10_0
                   (ite main@%_19_0
                        main@%spec.select1014_0
                        main@%spec.select13_0))
                (= main@%_20_0 @nd_0)
                (= main@%_22_0 (= main@%_21_0 main@%loop.bound_0))
                (=> main@swap_dec.exit_0
                    (and main@swap_dec.exit_0 main@tailrecurse.i_0))
                (=> (and main@swap_dec.exit_0 main@tailrecurse.i_0)
                    (not main@%_22_0))
                (=> main@swap_dec.exit_0
                    (= main@%.0.8.pre_0 (select main@%sm3_0 main@%_1_0)))
                (=> main@swap_dec.exit_0
                    (= main@%_23_0 (< main@%_4_0 main@%.0.8.pre_0)))
                (=> main@swap_dec.exit.thread_0
                    (and main@swap_dec.exit.thread_0 main@swap_dec.exit_0))
                (=> (and main@swap_dec.exit.thread_0 main@swap_dec.exit_0)
                    (not main@%_23_0))
                (=> (and main@swap_dec.exit.thread_0 main@swap_dec.exit_0)
                    (= main@%.0.817_0 main@%.0.8.pre_0))
                (=> (and main@swap_dec.exit.thread_0 main@swap_dec.exit_0)
                    (= main@%.0.817_1 main@%.0.817_0))
                (=> main@swap_dec.exit.thread_0
                    (= main@%_24_0 (- main@%_4_0 main@%.0.817_1)))
                (=> main@swap_dec.exit.thread_0
                    (= main@%_25_0 (< main@%_24_0 4)))
                (=> main@swap_dec.exit.thread_0 (not main@%_25_0))
                (=> |tuple(main@swap_dec.exit_0, main@verifier.error_0)|
                    main@swap_dec.exit_0)
                (=> main@verifier.error_0
                    (or |tuple(main@swap_dec.exit_0, main@verifier.error_0)|
                        (and main@verifier.error_0 main@swap_dec.exit.thread_0)))
                (=> |tuple(main@swap_dec.exit_0, main@verifier.error_0)|
                    main@%_23_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

