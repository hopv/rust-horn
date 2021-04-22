(set-info :original "09-lists/lists-4-inc-some2-safe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_list@_sm1 ((Array Int Int) Int ))
(declare-rel nd_list@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_list (Bool Bool Bool (Array Int Int) Int ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int (Array Int Int) Bool Int Int Int Int Int ))
(declare-rel main@tailrecurse.i1 (Int Int (Array Int Int) Int Bool Int Int Int ))
(declare-rel main@tailrecurse.i3 (Int (Array Int Int) Int Int Int Bool Int Int ))
(declare-rel main@tailrecurse.i9 ((Array Int Int) Int Int (Array Int Int) Int ))
(declare-rel main@sum.exit11.split ())
(declare-var nd_list@%_6_0 Int )
(declare-var nd_list@%sh_0 (Array Int Int) )
(declare-var nd_list@%_8_0 Int )
(declare-var nd_list@%_9_0 Int )
(declare-var nd_list@%_sm_0 Int )
(declare-var nd_list@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_2 Int )
(declare-var nd_list@%_2_0 Int )
(declare-var @nd_0 Int )
(declare-var nd_list@%_3_0 Int )
(declare-var nd_list@%_br_0 Bool )
(declare-var nd_list@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_0 Int )
(declare-var nd_list@%sm1_0 (Array Int Int) )
(declare-var nd_list@_sm1_0 Bool )
(declare-var nd_list@_br2_0 Bool )
(declare-var nd_list@_call_0 Bool )
(declare-var nd_list@%_sh_0 Int )
(declare-var nd_list@%sm_0 (Array Int Int) )
(declare-var nd_list@UnifiedReturnBlock_0 Bool )
(declare-var nd_list@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_1 Int )
(declare-var nd_list@UnifiedReturnBlock.split_0 Bool )
(declare-var main@%_16_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_40_0 Bool )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%.tr3.i7_2 Int )
(declare-var main@%accumulator.tr2.i8_2 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@%.tr1.i2.be_2 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%.tr1.i.be_2 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%.tr3.i_2 Int )
(declare-var main@%accumulator.tr2.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%.tr3.i_0 Int )
(declare-var main@%accumulator.tr2.i_0 Int )
(declare-var main@%.tr3.i_1 Int )
(declare-var main@%accumulator.tr2.i_1 Int )
(declare-var main@sum.exit_0 Bool )
(declare-var main@%accumulator.tr.lcssa.i_0 Int )
(declare-var main@%accumulator.tr.lcssa.i_1 Int )
(declare-var main@tailrecurse.i1_0 Bool )
(declare-var main@%.tr1.i_0 Int )
(declare-var main@%.tr1.i_1 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@sum.exit.loopexit_0 Bool )
(declare-var main@%phitmp_0 Int )
(declare-var main@_11_0 Bool )
(declare-var main@_15_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@tailrecurse.i1.backedge_0 Bool )
(declare-var |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)| Bool )
(declare-var main@%.tr1.i.be_0 Int )
(declare-var main@%.tr1.i.be_1 Int )
(declare-var main@tailrecurse.i1_1 Bool )
(declare-var main@%.tr1.i_2 Int )
(declare-var main@take_some_rest.exit_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@tailrecurse.i3_0 Bool )
(declare-var main@%.tr1.i2_0 Int )
(declare-var main@%.tr1.i2_1 Int )
(declare-var main@_22_0 Bool )
(declare-var main@_26_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@tailrecurse.i3.backedge_0 Bool )
(declare-var |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)| Bool )
(declare-var main@%.tr1.i2.be_0 Int )
(declare-var main@%.tr1.i2.be_1 Int )
(declare-var main@tailrecurse.i3_1 Bool )
(declare-var main@%.tr1.i2_2 Int )
(declare-var main@take_some_rest.exit6_0 Bool )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@tailrecurse.i9_0 Bool )
(declare-var main@%.tr3.i7_0 Int )
(declare-var main@%accumulator.tr2.i8_0 Int )
(declare-var main@%.tr3.i7_1 Int )
(declare-var main@%accumulator.tr2.i8_1 Int )
(declare-var main@sum.exit11_0 Bool )
(declare-var main@%accumulator.tr.lcssa.i10_0 Int )
(declare-var main@%accumulator.tr.lcssa.i10_1 Int )
(declare-var main@sum.exit11.split_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@tailrecurse.i9_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (nd_list true true true nd_list@%shadow.mem.0.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list false true true nd_list@%shadow.mem.0.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list false false false nd_list@%shadow.mem.0.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list@_sm1 nd_list@%sm1_0 @nd_0))
(rule (let ((a!1 (=> nd_list@_call_0 (= nd_list@%_9_0 (+ nd_list@%_6_0 (* 4 1))))))
(let ((a!2 (and (nd_list@_sm1 nd_list@%sm1_0 @nd_0)
                true
                (= nd_list@%_2_0 @nd_0)
                (= nd_list@%_br_0 (= nd_list@%_3_0 0))
                (=> nd_list@_br2_0 (and nd_list@_br2_0 nd_list@_sm1_0))
                (=> (and nd_list@_br2_0 nd_list@_sm1_0) (not nd_list@%_br_0))
                (=> nd_list@_call_0 (and nd_list@_call_0 nd_list@_sm1_0))
                (=> (and nd_list@_call_0 nd_list@_sm1_0) nd_list@%_br_0)
                (=> nd_list@_call_0 (= nd_list@%_sh_0 nd_list@%_6_0))
                (nd_list nd_list@_call_0
                         false
                         false
                         nd_list@%sh_0
                         nd_list@%_8_0)
                a!1
                (=> nd_list@_call_0
                    (or (<= nd_list@%_6_0 0) (> nd_list@%_9_0 0)))
                (=> nd_list@_call_0 (= nd_list@%_sm_0 nd_list@%_9_0))
                (=> nd_list@_call_0 (> nd_list@%_6_0 0))
                (=> nd_list@_call_0
                    (= nd_list@%sm_0
                       (store nd_list@%sh_0 nd_list@%_sm_0 nd_list@%_8_0)))
                (=> nd_list@UnifiedReturnBlock_0
                    (or (and nd_list@UnifiedReturnBlock_0 nd_list@_br2_0)
                        (and nd_list@UnifiedReturnBlock_0 nd_list@_call_0)))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br2_0)
                    (= nd_list@%shadow.mem.0.0_0 nd_list@%sm1_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br2_0)
                    (= nd_list@%UnifiedRetVal_0 0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_call_0)
                    (= nd_list@%shadow.mem.0.0_1 nd_list@%sm_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_call_0)
                    (= nd_list@%UnifiedRetVal_1 nd_list@%_sh_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br2_0)
                    (= nd_list@%shadow.mem.0.0_2 nd_list@%shadow.mem.0.0_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br2_0)
                    (= nd_list@%UnifiedRetVal_2 nd_list@%UnifiedRetVal_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_call_0)
                    (= nd_list@%shadow.mem.0.0_2 nd_list@%shadow.mem.0.0_1))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_call_0)
                    (= nd_list@%UnifiedRetVal_2 nd_list@%UnifiedRetVal_1))
                (=> nd_list@UnifiedReturnBlock.split_0
                    (and nd_list@UnifiedReturnBlock.split_0
                         nd_list@UnifiedReturnBlock_0))
                nd_list@UnifiedReturnBlock.split_0)))
  (=> a!2
      (nd_list@UnifiedReturnBlock.split
        nd_list@%shadow.mem.0.0_2
        nd_list@%UnifiedRetVal_2
        nd_list@%sm1_0
        @nd_0)))))
(rule (=> (nd_list@UnifiedReturnBlock.split
      nd_list@%shadow.mem.0.0_0
      nd_list@%UnifiedRetVal_0
      nd_list@%sm1_0
      @nd_0)
    (nd_list true
             false
             false
             nd_list@%shadow.mem.0.0_0
             nd_list@%UnifiedRetVal_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 0))
         main@%_1_0
         (nd_list true false false main@%sh_0 main@%_2_0)
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (not main@%_3_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%accumulator.tr2.i_0 0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_1 main@%.tr3.i_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%accumulator.tr2.i_1 main@%accumulator.tr2.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      @nd_0
      main@%sh_0
      main@%_3_0
      main@%_2_0
      main@%loop.bound_0
      main@%loop.bound1_0
      main@%.tr3.i_1
      main@%accumulator.tr2.i_1)))
(rule (=> (and (main@entry @nd_0)
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 0))
         main@%_1_0
         (nd_list true false false main@%sh_0 main@%_2_0)
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@sum.exit_0 (and main@sum.exit_0 main@entry_0))
         (=> (and main@sum.exit_0 main@entry_0) main@%_3_0)
         (=> (and main@sum.exit_0 main@entry_0)
             (= main@%accumulator.tr.lcssa.i_0 2))
         (=> (and main@sum.exit_0 main@entry_0)
             (= main@%accumulator.tr.lcssa.i_1 main@%accumulator.tr.lcssa.i_0))
         (=> main@tailrecurse.i1_0 (and main@tailrecurse.i1_0 main@sum.exit_0))
         (=> (and main@tailrecurse.i1_0 main@sum.exit_0)
             (= main@%.tr1.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i1_0 main@sum.exit_0)
             (= main@%.tr1.i_1 main@%.tr1.i_0))
         main@tailrecurse.i1_0)
    (main@tailrecurse.i1
      @nd_0
      main@%.tr1.i_1
      main@%sh_0
      main@%accumulator.tr.lcssa.i_1
      main@%_3_0
      main@%_2_0
      main@%loop.bound_0
      main@%loop.bound1_0)))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i
             @nd_0
             main@%sh_0
             main@%_3_0
             main@%_2_0
             main@%loop.bound_0
             main@%loop.bound1_0
             main@%.tr3.i_0
             main@%accumulator.tr2.i_0)
           true
           a!1
           (or (<= main@%.tr3.i_0 0) (> main@%_4_0 0))
           (= main@%_5_0 (select main@%sh_0 main@%_4_0))
           a!2
           (or (<= main@%.tr3.i_0 0) (> main@%_6_0 0))
           (> main@%.tr3.i_0 0)
           (= main@%_7_0 (select main@%sh_0 main@%_6_0))
           (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr2.i_0))
           (= main@%_9_0 (= main@%_7_0 0))
           (=> main@tailrecurse.i_1
               (and main@tailrecurse.i_1 main@tailrecurse.i_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_9_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr3.i_1 main@%_7_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr2.i_1 main@%_8_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr3.i_2 main@%.tr3.i_1))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr2.i_2 main@%accumulator.tr2.i_1))
           main@tailrecurse.i_1)
      (main@tailrecurse.i
        @nd_0
        main@%sh_0
        main@%_3_0
        main@%_2_0
        main@%loop.bound_0
        main@%loop.bound1_0
        main@%.tr3.i_2
        main@%accumulator.tr2.i_2))))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%sh_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.tr3.i_0
                  main@%accumulator.tr2.i_0)
                true
                a!1
                (or (<= main@%.tr3.i_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%sh_0 main@%_4_0))
                a!2
                (or (<= main@%.tr3.i_0 0) (> main@%_6_0 0))
                (> main@%.tr3.i_0 0)
                (= main@%_7_0 (select main@%sh_0 main@%_6_0))
                (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr2.i_0))
                (= main@%_9_0 (= main@%_7_0 0))
                (=> main@sum.exit.loopexit_0
                    (and main@sum.exit.loopexit_0 main@tailrecurse.i_0))
                (=> (and main@sum.exit.loopexit_0 main@tailrecurse.i_0)
                    main@%_9_0)
                (=> main@sum.exit.loopexit_0
                    (= main@%phitmp_0 (+ main@%_8_0 2)))
                (=> main@sum.exit_0
                    (and main@sum.exit_0 main@sum.exit.loopexit_0))
                (=> (and main@sum.exit_0 main@sum.exit.loopexit_0)
                    (= main@%accumulator.tr.lcssa.i_0 main@%phitmp_0))
                (=> (and main@sum.exit_0 main@sum.exit.loopexit_0)
                    (= main@%accumulator.tr.lcssa.i_1
                       main@%accumulator.tr.lcssa.i_0))
                (=> main@tailrecurse.i1_0
                    (and main@tailrecurse.i1_0 main@sum.exit_0))
                (=> (and main@tailrecurse.i1_0 main@sum.exit_0)
                    (= main@%.tr1.i_0 main@%_2_0))
                (=> (and main@tailrecurse.i1_0 main@sum.exit_0)
                    (= main@%.tr1.i_1 main@%.tr1.i_0))
                main@tailrecurse.i1_0)))
  (=> a!3
      (main@tailrecurse.i1
        @nd_0
        main@%.tr1.i_1
        main@%sh_0
        main@%accumulator.tr.lcssa.i_1
        main@%_3_0
        main@%_2_0
        main@%loop.bound_0
        main@%loop.bound1_0)))))
(rule (let ((a!1 (=> main@_15_0 (= main@%_16_0 (+ main@%.tr1.i_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.i_0
                  main@%sh_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_10_0 (= main@%.tr1.i_0 0))
                (=> main@_11_0 (and main@_11_0 main@tailrecurse.i1_0))
                (=> (and main@_11_0 main@tailrecurse.i1_0) (not main@%_10_0))
                (=> main@_11_0 (= main@%_12_0 @nd_0))
                (=> main@_11_0
                    (= main@%_14_0 (= main@%_13_0 main@%loop.bound1_0)))
                (=> main@_15_0 (and main@_15_0 main@_11_0))
                (=> (and main@_15_0 main@_11_0) main@%_14_0)
                a!1
                (=> main@_15_0 (or (<= main@%.tr1.i_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> main@%.tr1.i_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sh_0 main@%_16_0)))
                (=> |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)|
                    main@tailrecurse.i1_0)
                (=> main@tailrecurse.i1.backedge_0
                    (or (and main@tailrecurse.i1.backedge_0 main@_15_0)
                        |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)|))
                (=> |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)|
                    main@%_10_0)
                (=> (and main@tailrecurse.i1.backedge_0 main@_15_0)
                    (= main@%.tr1.i.be_0 main@%_17_0))
                (=> |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)|
                    (= main@%.tr1.i.be_1 0))
                (=> (and main@tailrecurse.i1.backedge_0 main@_15_0)
                    (= main@%.tr1.i.be_2 main@%.tr1.i.be_0))
                (=> |tuple(main@tailrecurse.i1_0, main@tailrecurse.i1.backedge_0)|
                    (= main@%.tr1.i.be_2 main@%.tr1.i.be_1))
                (=> main@tailrecurse.i1_1
                    (and main@tailrecurse.i1_1 main@tailrecurse.i1.backedge_0))
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.i1.backedge_0)
                    (= main@%.tr1.i_1 main@%.tr1.i.be_2))
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.i1.backedge_0)
                    (= main@%.tr1.i_2 main@%.tr1.i_1))
                main@tailrecurse.i1_1)))
  (=> a!2
      (main@tailrecurse.i1
        @nd_0
        main@%.tr1.i_2
        main@%sh_0
        main@%accumulator.tr.lcssa.i_0
        main@%_3_0
        main@%_2_0
        main@%loop.bound_0
        main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_18_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_19_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.i_0
                  main@%sh_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_10_0 (= main@%.tr1.i_0 0))
                (=> main@_11_0 (and main@_11_0 main@tailrecurse.i1_0))
                (=> (and main@_11_0 main@tailrecurse.i1_0) (not main@%_10_0))
                (=> main@_11_0 (= main@%_12_0 @nd_0))
                (=> main@_11_0
                    (= main@%_14_0 (= main@%_13_0 main@%loop.bound1_0)))
                (=> main@take_some_rest.exit_0
                    (and main@take_some_rest.exit_0 main@_11_0))
                (=> (and main@take_some_rest.exit_0 main@_11_0)
                    (not main@%_14_0))
                (=> main@take_some_rest.exit_0 a!1)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.i_0 0) (> main@%_18_0 0)))
                (=> main@take_some_rest.exit_0 a!2)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.i_0 0) (> main@%_19_0 0)))
                (=> main@take_some_rest.exit_0 (> main@%.tr1.i_0 0))
                (=> main@take_some_rest.exit_0
                    (= main@%_20_0 (select main@%sh_0 main@%_19_0)))
                (=> main@tailrecurse.i3_0
                    (and main@tailrecurse.i3_0 main@take_some_rest.exit_0))
                (=> (and main@tailrecurse.i3_0 main@take_some_rest.exit_0)
                    (= main@%.tr1.i2_0 main@%_20_0))
                (=> (and main@tailrecurse.i3_0 main@take_some_rest.exit_0)
                    (= main@%.tr1.i2_1 main@%.tr1.i2_0))
                main@tailrecurse.i3_0)))
  (=> a!3
      (main@tailrecurse.i3
        @nd_0
        main@%sh_0
        main@%.tr1.i2_1
        main@%accumulator.tr.lcssa.i_0
        main@%_18_0
        main@%_3_0
        main@%_2_0
        main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@_26_0 (= main@%_27_0 (+ main@%.tr1.i2_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i3
                  @nd_0
                  main@%sh_0
                  main@%.tr1.i2_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%_18_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0)
                true
                (= main@%_21_0 (= main@%.tr1.i2_0 0))
                (=> main@_22_0 (and main@_22_0 main@tailrecurse.i3_0))
                (=> (and main@_22_0 main@tailrecurse.i3_0) (not main@%_21_0))
                (=> main@_22_0 (= main@%_23_0 @nd_0))
                (=> main@_22_0
                    (= main@%_25_0 (= main@%_24_0 main@%loop.bound_0)))
                (=> main@_26_0 (and main@_26_0 main@_22_0))
                (=> (and main@_26_0 main@_22_0) main@%_25_0)
                a!1
                (=> main@_26_0 (or (<= main@%.tr1.i2_0 0) (> main@%_27_0 0)))
                (=> main@_26_0 (> main@%.tr1.i2_0 0))
                (=> main@_26_0 (= main@%_28_0 (select main@%sh_0 main@%_27_0)))
                (=> |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)|
                    main@tailrecurse.i3_0)
                (=> main@tailrecurse.i3.backedge_0
                    (or (and main@tailrecurse.i3.backedge_0 main@_26_0)
                        |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)|))
                (=> |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)|
                    main@%_21_0)
                (=> (and main@tailrecurse.i3.backedge_0 main@_26_0)
                    (= main@%.tr1.i2.be_0 main@%_28_0))
                (=> |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)|
                    (= main@%.tr1.i2.be_1 0))
                (=> (and main@tailrecurse.i3.backedge_0 main@_26_0)
                    (= main@%.tr1.i2.be_2 main@%.tr1.i2.be_0))
                (=> |tuple(main@tailrecurse.i3_0, main@tailrecurse.i3.backedge_0)|
                    (= main@%.tr1.i2.be_2 main@%.tr1.i2.be_1))
                (=> main@tailrecurse.i3_1
                    (and main@tailrecurse.i3_1 main@tailrecurse.i3.backedge_0))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3.backedge_0)
                    (= main@%.tr1.i2_1 main@%.tr1.i2.be_2))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3.backedge_0)
                    (= main@%.tr1.i2_2 main@%.tr1.i2_1))
                main@tailrecurse.i3_1)))
  (=> a!2
      (main@tailrecurse.i3
        @nd_0
        main@%sh_0
        main@%.tr1.i2_2
        main@%accumulator.tr.lcssa.i_0
        main@%_18_0
        main@%_3_0
        main@%_2_0
        main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@take_some_rest.exit6_0
               (= main@%_29_0 (+ main@%.tr1.i2_0 (* 0 8) 0)))))
(let ((a!2 (and (main@tailrecurse.i3
                  @nd_0
                  main@%sh_0
                  main@%.tr1.i2_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%_18_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0)
                true
                (= main@%_21_0 (= main@%.tr1.i2_0 0))
                (=> main@_22_0 (and main@_22_0 main@tailrecurse.i3_0))
                (=> (and main@_22_0 main@tailrecurse.i3_0) (not main@%_21_0))
                (=> main@_22_0 (= main@%_23_0 @nd_0))
                (=> main@_22_0
                    (= main@%_25_0 (= main@%_24_0 main@%loop.bound_0)))
                (=> main@take_some_rest.exit6_0
                    (and main@take_some_rest.exit6_0 main@_22_0))
                (=> (and main@take_some_rest.exit6_0 main@_22_0)
                    (not main@%_25_0))
                a!1
                (=> main@take_some_rest.exit6_0
                    (or (<= main@%.tr1.i2_0 0) (> main@%_29_0 0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_30_0 (select main@%sh_0 main@%_18_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_31_0 (+ main@%_30_0 1)))
                (=> main@take_some_rest.exit6_0
                    (= main@%sm_0 (store main@%sh_0 main@%_18_0 main@%_31_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_32_0 (select main@%sm_0 main@%_29_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_33_0 (+ main@%_32_0 1)))
                (=> main@take_some_rest.exit6_0
                    (= main@%sm2_0 (store main@%sm_0 main@%_29_0 main@%_33_0)))
                (=> main@tailrecurse.i9_0
                    (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0))
                (=> (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0)
                    (not main@%_3_0))
                (=> (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0)
                    (= main@%.tr3.i7_0 main@%_2_0))
                (=> (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0)
                    (= main@%accumulator.tr2.i8_0 0))
                (=> (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0)
                    (= main@%.tr3.i7_1 main@%.tr3.i7_0))
                (=> (and main@tailrecurse.i9_0 main@take_some_rest.exit6_0)
                    (= main@%accumulator.tr2.i8_1 main@%accumulator.tr2.i8_0))
                main@tailrecurse.i9_0)))
  (=> a!2
      (main@tailrecurse.i9
        main@%sh_0
        main@%accumulator.tr.lcssa.i_0
        main@%.tr3.i7_1
        main@%sm2_0
        main@%accumulator.tr2.i8_1)))))
(rule (let ((a!1 (=> main@take_some_rest.exit6_0
               (= main@%_29_0 (+ main@%.tr1.i2_0 (* 0 8) 0)))))
(let ((a!2 (and (main@tailrecurse.i3
                  @nd_0
                  main@%sh_0
                  main@%.tr1.i2_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%_18_0
                  main@%_3_0
                  main@%_2_0
                  main@%loop.bound_0)
                true
                (= main@%_21_0 (= main@%.tr1.i2_0 0))
                (=> main@_22_0 (and main@_22_0 main@tailrecurse.i3_0))
                (=> (and main@_22_0 main@tailrecurse.i3_0) (not main@%_21_0))
                (=> main@_22_0 (= main@%_23_0 @nd_0))
                (=> main@_22_0
                    (= main@%_25_0 (= main@%_24_0 main@%loop.bound_0)))
                (=> main@take_some_rest.exit6_0
                    (and main@take_some_rest.exit6_0 main@_22_0))
                (=> (and main@take_some_rest.exit6_0 main@_22_0)
                    (not main@%_25_0))
                a!1
                (=> main@take_some_rest.exit6_0
                    (or (<= main@%.tr1.i2_0 0) (> main@%_29_0 0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_30_0 (select main@%sh_0 main@%_18_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_31_0 (+ main@%_30_0 1)))
                (=> main@take_some_rest.exit6_0
                    (= main@%sm_0 (store main@%sh_0 main@%_18_0 main@%_31_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_32_0 (select main@%sm_0 main@%_29_0)))
                (=> main@take_some_rest.exit6_0
                    (= main@%_33_0 (+ main@%_32_0 1)))
                (=> main@take_some_rest.exit6_0
                    (= main@%sm2_0 (store main@%sm_0 main@%_29_0 main@%_33_0)))
                (=> main@sum.exit11_0
                    (and main@sum.exit11_0 main@take_some_rest.exit6_0))
                (=> (and main@sum.exit11_0 main@take_some_rest.exit6_0)
                    main@%_3_0)
                (=> (and main@sum.exit11_0 main@take_some_rest.exit6_0)
                    (= main@%accumulator.tr.lcssa.i10_0 0))
                (=> (and main@sum.exit11_0 main@take_some_rest.exit6_0)
                    (= main@%accumulator.tr.lcssa.i10_1
                       main@%accumulator.tr.lcssa.i10_0))
                (=> main@sum.exit11_0
                    (= main@%_40_0
                       (= main@%accumulator.tr.lcssa.i10_1
                          main@%accumulator.tr.lcssa.i_0)))
                (=> main@sum.exit11_0 (not main@%_40_0))
                (=> main@sum.exit11.split_0
                    (and main@sum.exit11.split_0 main@sum.exit11_0))
                main@sum.exit11.split_0)))
  (=> a!2 main@sum.exit11.split))))
(rule (let ((a!1 (= main@%_34_0 (+ (+ main@%.tr3.i7_0 (* 0 8)) 0)))
      (a!2 (= main@%_36_0 (+ (+ main@%.tr3.i7_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i9
             main@%sh_0
             main@%accumulator.tr.lcssa.i_0
             main@%.tr3.i7_0
             main@%sm2_0
             main@%accumulator.tr2.i8_0)
           true
           a!1
           (or (<= main@%.tr3.i7_0 0) (> main@%_34_0 0))
           (= main@%_35_0 (select main@%sm2_0 main@%_34_0))
           a!2
           (or (<= main@%.tr3.i7_0 0) (> main@%_36_0 0))
           (> main@%.tr3.i7_0 0)
           (= main@%_37_0 (select main@%sh_0 main@%_36_0))
           (= main@%_38_0 (+ main@%_35_0 main@%accumulator.tr2.i8_0))
           (= main@%_39_0 (= main@%_37_0 0))
           (=> main@tailrecurse.i9_1
               (and main@tailrecurse.i9_1 main@tailrecurse.i9_0))
           (=> (and main@tailrecurse.i9_1 main@tailrecurse.i9_0)
               (not main@%_39_0))
           (=> (and main@tailrecurse.i9_1 main@tailrecurse.i9_0)
               (= main@%.tr3.i7_1 main@%_37_0))
           (=> (and main@tailrecurse.i9_1 main@tailrecurse.i9_0)
               (= main@%accumulator.tr2.i8_1 main@%_38_0))
           (=> (and main@tailrecurse.i9_1 main@tailrecurse.i9_0)
               (= main@%.tr3.i7_2 main@%.tr3.i7_1))
           (=> (and main@tailrecurse.i9_1 main@tailrecurse.i9_0)
               (= main@%accumulator.tr2.i8_2 main@%accumulator.tr2.i8_1))
           main@tailrecurse.i9_1)
      (main@tailrecurse.i9
        main@%sh_0
        main@%accumulator.tr.lcssa.i_0
        main@%.tr3.i7_2
        main@%sm2_0
        main@%accumulator.tr2.i8_2))))
(rule (let ((a!1 (= main@%_34_0 (+ (+ main@%.tr3.i7_0 (* 0 8)) 0)))
      (a!2 (= main@%_36_0 (+ (+ main@%.tr3.i7_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i9
                  main@%sh_0
                  main@%accumulator.tr.lcssa.i_0
                  main@%.tr3.i7_0
                  main@%sm2_0
                  main@%accumulator.tr2.i8_0)
                true
                a!1
                (or (<= main@%.tr3.i7_0 0) (> main@%_34_0 0))
                (= main@%_35_0 (select main@%sm2_0 main@%_34_0))
                a!2
                (or (<= main@%.tr3.i7_0 0) (> main@%_36_0 0))
                (> main@%.tr3.i7_0 0)
                (= main@%_37_0 (select main@%sh_0 main@%_36_0))
                (= main@%_38_0 (+ main@%_35_0 main@%accumulator.tr2.i8_0))
                (= main@%_39_0 (= main@%_37_0 0))
                (=> main@sum.exit11_0
                    (and main@sum.exit11_0 main@tailrecurse.i9_0))
                (=> (and main@sum.exit11_0 main@tailrecurse.i9_0) main@%_39_0)
                (=> (and main@sum.exit11_0 main@tailrecurse.i9_0)
                    (= main@%accumulator.tr.lcssa.i10_0 main@%_38_0))
                (=> (and main@sum.exit11_0 main@tailrecurse.i9_0)
                    (= main@%accumulator.tr.lcssa.i10_1
                       main@%accumulator.tr.lcssa.i10_0))
                (=> main@sum.exit11_0
                    (= main@%_40_0
                       (= main@%accumulator.tr.lcssa.i10_1
                          main@%accumulator.tr.lcssa.i_0)))
                (=> main@sum.exit11_0 (not main@%_40_0))
                (=> main@sum.exit11.split_0
                    (and main@sum.exit11.split_0 main@sum.exit11_0))
                main@sum.exit11.split_0)))
  (=> a!3 main@sum.exit11.split))))
(query main@sum.exit11.split)

