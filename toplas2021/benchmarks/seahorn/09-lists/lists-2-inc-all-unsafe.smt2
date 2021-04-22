(set-info :original "09-lists/lists-2-inc-all-unsafe.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_list@_sm1 ((Array Int Int) Int ))
(declare-rel nd_list@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_list (Bool Bool Bool (Array Int Int) Int ))
(declare-rel main@entry ())
(declare-rel main@tailrecurse.i (Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i3 (Int Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i5 (Int Int Int Int (Array Int Int) ))
(declare-rel main@tailrecurse.i8 (Int (Array Int Int) Int Int Int ))
(declare-rel main@sum.exit10.split ())
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
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%.tr3.i6_2 Int )
(declare-var main@%accumulator.tr2.i7_2 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%.tr1.i_2 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%.tr3.i1_2 Int )
(declare-var main@%accumulator.tr2.i2_2 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%.tr3.i_2 Int )
(declare-var main@%accumulator.tr2.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%sh_0 (Array Int Int) )
(declare-var main@%_0_0 Int )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%.tr3.i_0 Int )
(declare-var main@%accumulator.tr2.i_0 Int )
(declare-var main@%.tr3.i_1 Int )
(declare-var main@%accumulator.tr2.i_1 Int )
(declare-var main@inc.exit.thread_0 Bool )
(declare-var main@sum.exit10_0 Bool )
(declare-var main@%accumulator.tr.lcssa.i121520_0 Int )
(declare-var main@%accumulator.tr.lcssa.i41619_0 Int )
(declare-var main@%accumulator.tr.lcssa.i9_0 Int )
(declare-var main@%accumulator.tr.lcssa.i121520_1 Int )
(declare-var main@%accumulator.tr.lcssa.i41619_1 Int )
(declare-var main@%accumulator.tr.lcssa.i9_1 Int )
(declare-var main@sum.exit10.split_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@tailrecurse.i3.preheader_0 Bool )
(declare-var main@tailrecurse.i3_0 Bool )
(declare-var main@%.tr3.i1_0 Int )
(declare-var main@%accumulator.tr2.i2_0 Int )
(declare-var main@%.tr3.i1_1 Int )
(declare-var main@%accumulator.tr2.i2_1 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@tailrecurse.i3_1 Bool )
(declare-var main@tailrecurse.i5.preheader_0 Bool )
(declare-var main@tailrecurse.i5_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.tr1.i_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.tr1.i_1 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%_16_0 Int )
(declare-var main@tailrecurse.i5_1 Bool )
(declare-var main@tailrecurse.i8.preheader_0 Bool )
(declare-var main@tailrecurse.i8_0 Bool )
(declare-var main@%.tr3.i6_0 Int )
(declare-var main@%accumulator.tr2.i7_0 Int )
(declare-var main@%.tr3.i6_1 Int )
(declare-var main@%accumulator.tr2.i7_1 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@tailrecurse.i8_1 Bool )
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
(rule main@entry)
(rule (=> (and main@entry
         true
         (nd_list true false false main@%sh_0 main@%_0_0)
         (= main@%_1_0 (= main@%_0_0 0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@entry_0))
         (=> (and main@tailrecurse.i_0 main@entry_0) (not main@%_1_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_0 main@%_0_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%accumulator.tr2.i_0 0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%.tr3.i_1 main@%.tr3.i_0))
         (=> (and main@tailrecurse.i_0 main@entry_0)
             (= main@%accumulator.tr2.i_1 main@%accumulator.tr2.i_0))
         main@tailrecurse.i_0)
    (main@tailrecurse.i
      main@%_0_0
      main@%sh_0
      main@%.tr3.i_1
      main@%accumulator.tr2.i_1)))
(rule (let ((a!1 (and main@entry
                true
                (nd_list true false false main@%sh_0 main@%_0_0)
                (= main@%_1_0 (= main@%_0_0 0))
                (=> main@inc.exit.thread_0
                    (and main@inc.exit.thread_0 main@entry_0))
                (=> (and main@inc.exit.thread_0 main@entry_0) main@%_1_0)
                (=> main@sum.exit10_0
                    (and main@sum.exit10_0 main@inc.exit.thread_0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i121520_0 0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i41619_0 0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i9_0 0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i121520_1
                       main@%accumulator.tr.lcssa.i121520_0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i41619_1
                       main@%accumulator.tr.lcssa.i41619_0))
                (=> (and main@sum.exit10_0 main@inc.exit.thread_0)
                    (= main@%accumulator.tr.lcssa.i9_1
                       main@%accumulator.tr.lcssa.i9_0))
                (=> main@sum.exit10_0
                    (= main@%_24_0
                       (+ main@%accumulator.tr.lcssa.i41619_1
                          main@%accumulator.tr.lcssa.i121520_1)))
                (=> main@sum.exit10_0
                    (= main@%_25_0
                       (> main@%accumulator.tr.lcssa.i9_1 main@%_24_0)))
                (=> main@sum.exit10_0 (not main@%_25_0))
                (=> main@sum.exit10.split_0
                    (and main@sum.exit10.split_0 main@sum.exit10_0))
                main@sum.exit10.split_0)))
  (=> a!1 main@sum.exit10.split)))
(rule (let ((a!1 (= main@%_2_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_4_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i
             main@%_0_0
             main@%sh_0
             main@%.tr3.i_0
             main@%accumulator.tr2.i_0)
           true
           a!1
           (or (<= main@%.tr3.i_0 0) (> main@%_2_0 0))
           (= main@%_3_0 (select main@%sh_0 main@%_2_0))
           a!2
           (or (<= main@%.tr3.i_0 0) (> main@%_4_0 0))
           (> main@%.tr3.i_0 0)
           (= main@%_5_0 (select main@%sh_0 main@%_4_0))
           (= main@%_6_0 (+ main@%_3_0 main@%accumulator.tr2.i_0))
           (= main@%_7_0 (= main@%_5_0 0))
           (=> main@tailrecurse.i_1
               (and main@tailrecurse.i_1 main@tailrecurse.i_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_7_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr3.i_1 main@%_5_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr2.i_1 main@%_6_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr3.i_2 main@%.tr3.i_1))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr2.i_2 main@%accumulator.tr2.i_1))
           main@tailrecurse.i_1)
      (main@tailrecurse.i
        main@%_0_0
        main@%sh_0
        main@%.tr3.i_2
        main@%accumulator.tr2.i_2))))
(rule (let ((a!1 (= main@%_2_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_4_0 (+ (+ main@%.tr3.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i
             main@%_0_0
             main@%sh_0
             main@%.tr3.i_0
             main@%accumulator.tr2.i_0)
           true
           a!1
           (or (<= main@%.tr3.i_0 0) (> main@%_2_0 0))
           (= main@%_3_0 (select main@%sh_0 main@%_2_0))
           a!2
           (or (<= main@%.tr3.i_0 0) (> main@%_4_0 0))
           (> main@%.tr3.i_0 0)
           (= main@%_5_0 (select main@%sh_0 main@%_4_0))
           (= main@%_6_0 (+ main@%_3_0 main@%accumulator.tr2.i_0))
           (= main@%_7_0 (= main@%_5_0 0))
           (=> main@tailrecurse.i3.preheader_0
               (and main@tailrecurse.i3.preheader_0 main@tailrecurse.i_0))
           (=> (and main@tailrecurse.i3.preheader_0 main@tailrecurse.i_0)
               main@%_7_0)
           (=> main@tailrecurse.i3_0
               (and main@tailrecurse.i3_0 main@tailrecurse.i3.preheader_0))
           (=> (and main@tailrecurse.i3_0 main@tailrecurse.i3.preheader_0)
               (= main@%.tr3.i1_0 main@%_0_0))
           (=> (and main@tailrecurse.i3_0 main@tailrecurse.i3.preheader_0)
               (= main@%accumulator.tr2.i2_0 0))
           (=> (and main@tailrecurse.i3_0 main@tailrecurse.i3.preheader_0)
               (= main@%.tr3.i1_1 main@%.tr3.i1_0))
           (=> (and main@tailrecurse.i3_0 main@tailrecurse.i3.preheader_0)
               (= main@%accumulator.tr2.i2_1 main@%accumulator.tr2.i2_0))
           main@tailrecurse.i3_0)
      (main@tailrecurse.i3
        main@%_6_0
        main@%_0_0
        main@%sh_0
        main@%.tr3.i1_1
        main@%accumulator.tr2.i2_1))))
(rule (let ((a!1 (and (main@tailrecurse.i3
                  main@%_6_0
                  main@%_0_0
                  main@%sh_0
                  main@%.tr3.i1_0
                  main@%accumulator.tr2.i2_0)
                true
                (= main@%_8_0 (+ main@%.tr3.i1_0 (* 0 8) 4))
                (or (<= main@%.tr3.i1_0 0) (> main@%_8_0 0))
                (> main@%.tr3.i1_0 0)
                (= main@%_9_0 (select main@%sh_0 main@%_8_0))
                (= main@%_10_0 (+ main@%accumulator.tr2.i2_0 1))
                (= main@%_11_0 (= main@%_9_0 0))
                (=> main@tailrecurse.i3_1
                    (and main@tailrecurse.i3_1 main@tailrecurse.i3_0))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3_0)
                    (not main@%_11_0))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3_0)
                    (= main@%.tr3.i1_1 main@%_9_0))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3_0)
                    (= main@%accumulator.tr2.i2_1 main@%_10_0))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3_0)
                    (= main@%.tr3.i1_2 main@%.tr3.i1_1))
                (=> (and main@tailrecurse.i3_1 main@tailrecurse.i3_0)
                    (= main@%accumulator.tr2.i2_2 main@%accumulator.tr2.i2_1))
                main@tailrecurse.i3_1)))
  (=> a!1
      (main@tailrecurse.i3
        main@%_6_0
        main@%_0_0
        main@%sh_0
        main@%.tr3.i1_2
        main@%accumulator.tr2.i2_2))))
(rule (let ((a!1 (and (main@tailrecurse.i3
                  main@%_6_0
                  main@%_0_0
                  main@%sh_0
                  main@%.tr3.i1_0
                  main@%accumulator.tr2.i2_0)
                true
                (= main@%_8_0 (+ main@%.tr3.i1_0 (* 0 8) 4))
                (or (<= main@%.tr3.i1_0 0) (> main@%_8_0 0))
                (> main@%.tr3.i1_0 0)
                (= main@%_9_0 (select main@%sh_0 main@%_8_0))
                (= main@%_10_0 (+ main@%accumulator.tr2.i2_0 1))
                (= main@%_11_0 (= main@%_9_0 0))
                (=> main@tailrecurse.i5.preheader_0
                    (and main@tailrecurse.i5.preheader_0 main@tailrecurse.i3_0))
                (=> (and main@tailrecurse.i5.preheader_0 main@tailrecurse.i3_0)
                    main@%_11_0)
                (=> main@tailrecurse.i5_0
                    (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0))
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%shadow.mem.0.0_0 main@%sh_0))
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%.tr1.i_0 main@%_0_0))
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%.tr1.i_1 main@%.tr1.i_0))
                main@tailrecurse.i5_0)))
  (=> a!1
      (main@tailrecurse.i5
        main@%_6_0
        main@%_10_0
        main@%_0_0
        main@%.tr1.i_1
        main@%shadow.mem.0.0_1))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_15_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i5
             main@%_6_0
             main@%_10_0
             main@%_0_0
             main@%.tr1.i_0
             main@%shadow.mem.0.0_0)
           true
           a!1
           (or (<= main@%.tr1.i_0 0) (> main@%_12_0 0))
           (= main@%_13_0 (select main@%shadow.mem.0.0_0 main@%_12_0))
           (= main@%_14_0 (+ main@%_13_0 1))
           (= main@%sm_0 (store main@%shadow.mem.0.0_0 main@%_12_0 main@%_14_0))
           a!2
           (or (<= main@%.tr1.i_0 0) (> main@%_15_0 0))
           (> main@%.tr1.i_0 0)
           (= main@%_16_0 (select main@%sm_0 main@%_15_0))
           (= main@%_17_0 (= main@%_16_0 0))
           (=> main@tailrecurse.i5_1
               (and main@tailrecurse.i5_1 main@tailrecurse.i5_0))
           (=> (and main@tailrecurse.i5_1 main@tailrecurse.i5_0)
               (not main@%_17_0))
           (=> (and main@tailrecurse.i5_1 main@tailrecurse.i5_0)
               (= main@%shadow.mem.0.0_1 main@%sm_0))
           (=> (and main@tailrecurse.i5_1 main@tailrecurse.i5_0)
               (= main@%.tr1.i_1 main@%_16_0))
           (=> (and main@tailrecurse.i5_1 main@tailrecurse.i5_0)
               (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
           (=> (and main@tailrecurse.i5_1 main@tailrecurse.i5_0)
               (= main@%.tr1.i_2 main@%.tr1.i_1))
           main@tailrecurse.i5_1)
      (main@tailrecurse.i5
        main@%_6_0
        main@%_10_0
        main@%_0_0
        main@%.tr1.i_2
        main@%shadow.mem.0.0_2))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_15_0 (+ (+ main@%.tr1.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i5
             main@%_6_0
             main@%_10_0
             main@%_0_0
             main@%.tr1.i_0
             main@%shadow.mem.0.0_0)
           true
           a!1
           (or (<= main@%.tr1.i_0 0) (> main@%_12_0 0))
           (= main@%_13_0 (select main@%shadow.mem.0.0_0 main@%_12_0))
           (= main@%_14_0 (+ main@%_13_0 1))
           (= main@%sm_0 (store main@%shadow.mem.0.0_0 main@%_12_0 main@%_14_0))
           a!2
           (or (<= main@%.tr1.i_0 0) (> main@%_15_0 0))
           (> main@%.tr1.i_0 0)
           (= main@%_16_0 (select main@%sm_0 main@%_15_0))
           (= main@%_17_0 (= main@%_16_0 0))
           (=> main@tailrecurse.i8.preheader_0
               (and main@tailrecurse.i8.preheader_0 main@tailrecurse.i5_0))
           (=> (and main@tailrecurse.i8.preheader_0 main@tailrecurse.i5_0)
               main@%_17_0)
           (=> main@tailrecurse.i8_0
               (and main@tailrecurse.i8_0 main@tailrecurse.i8.preheader_0))
           (=> (and main@tailrecurse.i8_0 main@tailrecurse.i8.preheader_0)
               (= main@%.tr3.i6_0 main@%_0_0))
           (=> (and main@tailrecurse.i8_0 main@tailrecurse.i8.preheader_0)
               (= main@%accumulator.tr2.i7_0 0))
           (=> (and main@tailrecurse.i8_0 main@tailrecurse.i8.preheader_0)
               (= main@%.tr3.i6_1 main@%.tr3.i6_0))
           (=> (and main@tailrecurse.i8_0 main@tailrecurse.i8.preheader_0)
               (= main@%accumulator.tr2.i7_1 main@%accumulator.tr2.i7_0))
           main@tailrecurse.i8_0)
      (main@tailrecurse.i8
        main@%.tr3.i6_1
        main@%sm_0
        main@%accumulator.tr2.i7_1
        main@%_6_0
        main@%_10_0))))
(rule (let ((a!1 (= main@%_18_0 (+ (+ main@%.tr3.i6_0 (* 0 8)) 0)))
      (a!2 (= main@%_20_0 (+ (+ main@%.tr3.i6_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i8
             main@%.tr3.i6_0
             main@%sm_0
             main@%accumulator.tr2.i7_0
             main@%_6_0
             main@%_10_0)
           true
           a!1
           (or (<= main@%.tr3.i6_0 0) (> main@%_18_0 0))
           (= main@%_19_0 (select main@%sm_0 main@%_18_0))
           a!2
           (or (<= main@%.tr3.i6_0 0) (> main@%_20_0 0))
           (> main@%.tr3.i6_0 0)
           (= main@%_21_0 (select main@%sm_0 main@%_20_0))
           (= main@%_22_0 (+ main@%_19_0 main@%accumulator.tr2.i7_0))
           (= main@%_23_0 (= main@%_21_0 0))
           (=> main@tailrecurse.i8_1
               (and main@tailrecurse.i8_1 main@tailrecurse.i8_0))
           (=> (and main@tailrecurse.i8_1 main@tailrecurse.i8_0)
               (not main@%_23_0))
           (=> (and main@tailrecurse.i8_1 main@tailrecurse.i8_0)
               (= main@%.tr3.i6_1 main@%_21_0))
           (=> (and main@tailrecurse.i8_1 main@tailrecurse.i8_0)
               (= main@%accumulator.tr2.i7_1 main@%_22_0))
           (=> (and main@tailrecurse.i8_1 main@tailrecurse.i8_0)
               (= main@%.tr3.i6_2 main@%.tr3.i6_1))
           (=> (and main@tailrecurse.i8_1 main@tailrecurse.i8_0)
               (= main@%accumulator.tr2.i7_2 main@%accumulator.tr2.i7_1))
           main@tailrecurse.i8_1)
      (main@tailrecurse.i8
        main@%.tr3.i6_2
        main@%sm_0
        main@%accumulator.tr2.i7_2
        main@%_6_0
        main@%_10_0))))
(rule (let ((a!1 (= main@%_18_0 (+ (+ main@%.tr3.i6_0 (* 0 8)) 0)))
      (a!2 (= main@%_20_0 (+ (+ main@%.tr3.i6_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i8
                  main@%.tr3.i6_0
                  main@%sm_0
                  main@%accumulator.tr2.i7_0
                  main@%_6_0
                  main@%_10_0)
                true
                a!1
                (or (<= main@%.tr3.i6_0 0) (> main@%_18_0 0))
                (= main@%_19_0 (select main@%sm_0 main@%_18_0))
                a!2
                (or (<= main@%.tr3.i6_0 0) (> main@%_20_0 0))
                (> main@%.tr3.i6_0 0)
                (= main@%_21_0 (select main@%sm_0 main@%_20_0))
                (= main@%_22_0 (+ main@%_19_0 main@%accumulator.tr2.i7_0))
                (= main@%_23_0 (= main@%_21_0 0))
                (=> main@sum.exit10_0
                    (and main@sum.exit10_0 main@tailrecurse.i8_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0) main@%_23_0)
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i121520_0 main@%_6_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i41619_0 main@%_10_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i9_0 main@%_22_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i121520_1
                       main@%accumulator.tr.lcssa.i121520_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i41619_1
                       main@%accumulator.tr.lcssa.i41619_0))
                (=> (and main@sum.exit10_0 main@tailrecurse.i8_0)
                    (= main@%accumulator.tr.lcssa.i9_1
                       main@%accumulator.tr.lcssa.i9_0))
                (=> main@sum.exit10_0
                    (= main@%_24_0
                       (+ main@%accumulator.tr.lcssa.i41619_1
                          main@%accumulator.tr.lcssa.i121520_1)))
                (=> main@sum.exit10_0
                    (= main@%_25_0
                       (> main@%accumulator.tr.lcssa.i9_1 main@%_24_0)))
                (=> main@sum.exit10_0 (not main@%_25_0))
                (=> main@sum.exit10.split_0
                    (and main@sum.exit10.split_0 main@sum.exit10_0))
                main@sum.exit10.split_0)))
  (=> a!3 main@sum.exit10.split))))
(query main@sum.exit10.split)

