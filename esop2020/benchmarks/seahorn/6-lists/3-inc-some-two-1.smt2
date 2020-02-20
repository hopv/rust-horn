(set-info :original "6-lists/3-inc-some-two-1.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_list@_1 ((Array Int Int) Int ))
(declare-rel nd_list@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_list (Bool Bool Bool (Array Int Int) Int ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int (Array Int Int) Int Bool Int Int ))
(declare-rel main@tailrecurse.i1 (Int Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i5 (Int Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i11 (Int Int (Array Int Int) Int ))
(declare-rel main@sum.exit13.split ())
(declare-rel main@tailrecurse.us.i4 ())
(declare-rel main@tailrecurse.us.i ())
(declare-var nd_list@%_7_0 Int )
(declare-var nd_list@%_9_0 (Array Int Int) )
(declare-var nd_list@%_10_0 Int )
(declare-var nd_list@%_11_0 Int )
(declare-var nd_list@%_12_0 Int )
(declare-var nd_list@%_tail_0 (Array Int Int) )
(declare-var nd_list@%shadow.mem.0_2 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_2 Int )
(declare-var nd_list@%_3_0 Int )
(declare-var @nd_0 Int )
(declare-var nd_list@%_4_0 Int )
(declare-var nd_list@%_br_0 Bool )
(declare-var nd_list@%shadow.mem.0_0 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_0 Int )
(declare-var nd_list@_1_0 Bool )
(declare-var nd_list@_br1_0 Bool )
(declare-var nd_list@_6_0 Bool )
(declare-var nd_list@%_8_0 Int )
(declare-var nd_list@%_store_0 (Array Int Int) )
(declare-var nd_list@UnifiedReturnBlock_0 Bool )
(declare-var nd_list@%shadow.mem.0_1 (Array Int Int) )
(declare-var nd_list@%UnifiedRetVal_1 Int )
(declare-var nd_list@UnifiedReturnBlock.split_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%_39_0 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%.lcssa_1 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%xs.tr2.i9_2 Int )
(declare-var main@%accumulator.tr1.i10_2 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%xs.tr.ph.i217.lcssa_1 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%xs.tr.ph.i18.lcssa_1 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%.lcssa33_1 Int )
(declare-var main@%xs.tr2.i_2 Int )
(declare-var main@%accumulator.tr1.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Bool )
(declare-var main@tailrecurse.i.preheader_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%xs.tr2.i_0 Int )
(declare-var main@%accumulator.tr1.i_0 Int )
(declare-var main@%xs.tr2.i_1 Int )
(declare-var main@%accumulator.tr1.i_1 Int )
(declare-var main@tailrecurse.us.i.preheader_0 Bool )
(declare-var main@tailrecurse.us.i_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@sum.exit_0 Bool )
(declare-var main@%.lcssa33_0 Int )
(declare-var main@%phitmp_0 Int )
(declare-var main@tailrecurse.i1.preheader_0 Bool )
(declare-var main@tailrecurse.i1_0 Bool )
(declare-var main@%xs.tr.ph.i18_0 Int )
(declare-var main@%xs.tr.ph.i18_1 Int )
(declare-var main@tailrecurse.outer.i_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@tailrecurse.i1_1 Bool )
(declare-var main@%xs.tr.ph.i18_2 Int )
(declare-var main@some.exit_0 Bool )
(declare-var main@%xs.tr.ph.i18.lcssa_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_21_0 (Array Int Int) )
(declare-var main@tailrecurse.i5.preheader_0 Bool )
(declare-var main@tailrecurse.i5_0 Bool )
(declare-var main@%xs.tr.ph.i217_0 Int )
(declare-var main@%xs.tr.ph.i217_1 Int )
(declare-var main@tailrecurse.us.i4.preheader_0 Bool )
(declare-var main@tailrecurse.us.i4_0 Bool )
(declare-var main@tailrecurse.us.i.preheader.loopexit_0 Bool )
(declare-var main@tailrecurse.outer.i3_0 Bool )
(declare-var main@%_27_0 Int )
(declare-var main@tailrecurse.i5_1 Bool )
(declare-var main@%xs.tr.ph.i217_2 Int )
(declare-var main@tailrecurse.i11.preheader_0 Bool )
(declare-var main@%xs.tr.ph.i217.lcssa_0 Int )
(declare-var main@%_32_0 (Array Int Int) )
(declare-var main@tailrecurse.i11_0 Bool )
(declare-var main@%xs.tr2.i9_0 Int )
(declare-var main@%accumulator.tr1.i10_0 Int )
(declare-var main@%xs.tr2.i9_1 Int )
(declare-var main@%accumulator.tr1.i10_1 Int )
(declare-var main@tailrecurse.us.i4.preheader.loopexit_0 Bool )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@tailrecurse.i11_1 Bool )
(declare-var main@sum.exit13_0 Bool )
(declare-var main@%.lcssa_0 Int )
(declare-var main@sum.exit13.split_0 Bool )
(declare-var main@tailrecurse.us.i4_1 Bool )
(declare-var main@tailrecurse.us.i_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (nd_list true true true nd_list@%shadow.mem.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list false true true nd_list@%shadow.mem.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list false false false nd_list@%shadow.mem.0_0 nd_list@%UnifiedRetVal_0))
(rule (nd_list@_1 nd_list@%_tail_0 @nd_0))
(rule (let ((a!1 (=> nd_list@_6_0 (= nd_list@%_11_0 (+ nd_list@%_7_0 (* 4 1))))))
(let ((a!2 (and (nd_list@_1 nd_list@%_tail_0 @nd_0)
                true
                (= nd_list@%_3_0 @nd_0)
                (= nd_list@%_br_0 (= nd_list@%_4_0 0))
                (=> nd_list@_br1_0 (and nd_list@_br1_0 nd_list@_1_0))
                (=> (and nd_list@_br1_0 nd_list@_1_0) (not nd_list@%_br_0))
                (=> nd_list@_6_0 (and nd_list@_6_0 nd_list@_1_0))
                (=> (and nd_list@_6_0 nd_list@_1_0) nd_list@%_br_0)
                (=> nd_list@_6_0 (= nd_list@%_8_0 nd_list@%_7_0))
                (nd_list nd_list@_6_0 false false nd_list@%_9_0 nd_list@%_10_0)
                a!1
                (=> nd_list@_6_0 (or (<= nd_list@%_7_0 0) (> nd_list@%_11_0 0)))
                (=> nd_list@_6_0 (= nd_list@%_12_0 nd_list@%_11_0))
                (=> nd_list@_6_0 (> nd_list@%_7_0 0))
                (=> nd_list@_6_0
                    (= nd_list@%_store_0
                       (store nd_list@%_9_0 nd_list@%_12_0 nd_list@%_10_0)))
                (=> nd_list@UnifiedReturnBlock_0
                    (or (and nd_list@UnifiedReturnBlock_0 nd_list@_br1_0)
                        (and nd_list@UnifiedReturnBlock_0 nd_list@_6_0)))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br1_0)
                    (= nd_list@%shadow.mem.0_0 nd_list@%_tail_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br1_0)
                    (= nd_list@%UnifiedRetVal_0 0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_6_0)
                    (= nd_list@%shadow.mem.0_1 nd_list@%_store_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_6_0)
                    (= nd_list@%UnifiedRetVal_1 nd_list@%_8_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br1_0)
                    (= nd_list@%shadow.mem.0_2 nd_list@%shadow.mem.0_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_br1_0)
                    (= nd_list@%UnifiedRetVal_2 nd_list@%UnifiedRetVal_0))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_6_0)
                    (= nd_list@%shadow.mem.0_2 nd_list@%shadow.mem.0_1))
                (=> (and nd_list@UnifiedReturnBlock_0 nd_list@_6_0)
                    (= nd_list@%UnifiedRetVal_2 nd_list@%UnifiedRetVal_1))
                (=> nd_list@UnifiedReturnBlock.split_0
                    (and nd_list@UnifiedReturnBlock.split_0
                         nd_list@UnifiedReturnBlock_0))
                nd_list@UnifiedReturnBlock.split_0)))
  (=> a!2
      (nd_list@UnifiedReturnBlock.split
        nd_list@%shadow.mem.0_2
        nd_list@%UnifiedRetVal_2
        nd_list@%_tail_0
        @nd_0)))))
(rule (=> (nd_list@UnifiedReturnBlock.split
      nd_list@%shadow.mem.0_0
      nd_list@%UnifiedRetVal_0
      nd_list@%_tail_0
      @nd_0)
    (nd_list true false false nd_list@%shadow.mem.0_0 nd_list@%UnifiedRetVal_0)))
(rule (main@entry @nd_0))
(rule (=> (and (main@entry @nd_0)
         true
         (nd_list true false false main@%_1_0 main@%_2_0)
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@tailrecurse.i.preheader_0
             (and main@tailrecurse.i.preheader_0 main@entry_0))
         (=> (and main@tailrecurse.i.preheader_0 main@entry_0) (not main@%_3_0))
         (=> main@tailrecurse.i_0
             (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%xs.tr2.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%accumulator.tr1.i_0 0))
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%xs.tr2.i_1 main@%xs.tr2.i_0))
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%accumulator.tr1.i_1 main@%accumulator.tr1.i_0)))
    (main@tailrecurse.i
      @nd_0
      main@%_1_0
      main@%_2_0
      main@%_3_0
      main@%xs.tr2.i_1
      main@%accumulator.tr1.i_1)))
(rule (=> (and (main@entry @nd_0)
         true
         (nd_list true false false main@%_1_0 main@%_2_0)
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@tailrecurse.us.i.preheader_0
             (and main@tailrecurse.us.i.preheader_0 main@entry_0))
         (=> (and main@tailrecurse.us.i.preheader_0 main@entry_0) main@%_3_0)
         (=> main@tailrecurse.us.i_0
             (and main@tailrecurse.us.i_0 main@tailrecurse.us.i.preheader_0))
         main@tailrecurse.us.i_0)
    main@tailrecurse.us.i))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i
             @nd_0
             main@%_1_0
             main@%_2_0
             main@%_3_0
             main@%xs.tr2.i_0
             main@%accumulator.tr1.i_0)
           true
           a!1
           (or (<= main@%xs.tr2.i_0 0) (> main@%_4_0 0))
           (= main@%_5_0 (select main@%_1_0 main@%_4_0))
           a!2
           (or (<= main@%xs.tr2.i_0 0) (> main@%_6_0 0))
           (> main@%xs.tr2.i_0 0)
           (= main@%_7_0 (select main@%_1_0 main@%_6_0))
           (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
           (= main@%_9_0 (= main@%_7_0 0))
           (=> main@tailrecurse.i_1
               (and main@tailrecurse.i_1 main@tailrecurse.i_0))
           main@tailrecurse.i_1
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_9_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%xs.tr2.i_1 main@%_7_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr1.i_1 main@%_8_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%xs.tr2.i_2 main@%xs.tr2.i_1))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr1.i_2 main@%accumulator.tr1.i_1)))
      (main@tailrecurse.i
        @nd_0
        main@%_1_0
        main@%_2_0
        main@%_3_0
        main@%xs.tr2.i_2
        main@%accumulator.tr1.i_2))))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%_1_0
                  main@%_2_0
                  main@%_3_0
                  main@%xs.tr2.i_0
                  main@%accumulator.tr1.i_0)
                true
                a!1
                (or (<= main@%xs.tr2.i_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%_1_0 main@%_4_0))
                a!2
                (or (<= main@%xs.tr2.i_0 0) (> main@%_6_0 0))
                (> main@%xs.tr2.i_0 0)
                (= main@%_7_0 (select main@%_1_0 main@%_6_0))
                (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
                (= main@%_9_0 (= main@%_7_0 0))
                (=> main@sum.exit_0 (and main@sum.exit_0 main@tailrecurse.i_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0) main@%_9_0)
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa33_0 main@%_8_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa33_1 main@%.lcssa33_0))
                (=> main@sum.exit_0 (= main@%phitmp_0 (+ main@%.lcssa33_1 2)))
                (=> main@tailrecurse.i1.preheader_0
                    (and main@tailrecurse.i1.preheader_0 main@sum.exit_0))
                (=> (and main@tailrecurse.i1.preheader_0 main@sum.exit_0)
                    (not main@%_3_0))
                (=> main@tailrecurse.i1_0
                    (and main@tailrecurse.i1_0 main@tailrecurse.i1.preheader_0))
                main@tailrecurse.i1_0
                (=> (and main@tailrecurse.i1_0 main@tailrecurse.i1.preheader_0)
                    (= main@%xs.tr.ph.i18_0 main@%_2_0))
                (=> (and main@tailrecurse.i1_0 main@tailrecurse.i1.preheader_0)
                    (= main@%xs.tr.ph.i18_1 main@%xs.tr.ph.i18_0)))))
  (=> a!3
      (main@tailrecurse.i1
        @nd_0
        main@%xs.tr.ph.i18_1
        main@%_1_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%xs.tr2.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%_1_0
                  main@%_2_0
                  main@%_3_0
                  main@%xs.tr2.i_0
                  main@%accumulator.tr1.i_0)
                true
                a!1
                (or (<= main@%xs.tr2.i_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%_1_0 main@%_4_0))
                a!2
                (or (<= main@%xs.tr2.i_0 0) (> main@%_6_0 0))
                (> main@%xs.tr2.i_0 0)
                (= main@%_7_0 (select main@%_1_0 main@%_6_0))
                (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
                (= main@%_9_0 (= main@%_7_0 0))
                (=> main@sum.exit_0 (and main@sum.exit_0 main@tailrecurse.i_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0) main@%_9_0)
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa33_0 main@%_8_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa33_1 main@%.lcssa33_0))
                (=> main@sum.exit_0 (= main@%phitmp_0 (+ main@%.lcssa33_1 2)))
                (=> main@tailrecurse.us.i.preheader_0
                    (and main@tailrecurse.us.i.preheader_0 main@sum.exit_0))
                (=> (and main@tailrecurse.us.i.preheader_0 main@sum.exit_0)
                    main@%_3_0)
                (=> main@tailrecurse.us.i_0
                    (and main@tailrecurse.us.i_0
                         main@tailrecurse.us.i.preheader_0))
                main@tailrecurse.us.i_0)))
  (=> a!3 main@tailrecurse.us.i))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i_0
               (= main@%_13_0 (+ main@%xs.tr.ph.i18_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i1
                  @nd_0
                  main@%xs.tr.ph.i18_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@tailrecurse.outer.i_0
                    (and main@tailrecurse.outer.i_0 main@tailrecurse.i1_0))
                (=> (and main@tailrecurse.outer.i_0 main@tailrecurse.i1_0)
                    main@%_12_0)
                a!1
                (=> main@tailrecurse.outer.i_0
                    (or (<= main@%xs.tr.ph.i18_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.i_0 (> main@%xs.tr.ph.i18_0 0))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_14_0 (select main@%_1_0 main@%_13_0)))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_15_0 (= main@%_14_0 0)))
                (=> main@tailrecurse.i1_1
                    (and main@tailrecurse.i1_1 main@tailrecurse.outer.i_0))
                main@tailrecurse.i1_1
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.outer.i_0)
                    (not main@%_15_0))
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.outer.i_0)
                    (= main@%xs.tr.ph.i18_1 main@%_14_0))
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.outer.i_0)
                    (= main@%xs.tr.ph.i18_2 main@%xs.tr.ph.i18_1)))))
  (=> a!2
      (main@tailrecurse.i1
        @nd_0
        main@%xs.tr.ph.i18_2
        main@%_1_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_16_0 (+ (+ main@%xs.tr.ph.i18.lcssa_1 (* 0 8)) 0)))
      (a!2 (= main@%_17_0 (+ (+ main@%xs.tr.ph.i18.lcssa_1 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i1
                  @nd_0
                  main@%xs.tr.ph.i18_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@some.exit_0
                    (and main@some.exit_0 main@tailrecurse.i1_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (not main@%_12_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (= main@%xs.tr.ph.i18.lcssa_0 main@%xs.tr.ph.i18_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (= main@%xs.tr.ph.i18.lcssa_1 main@%xs.tr.ph.i18.lcssa_0))
                (=> main@some.exit_0 a!1)
                (=> main@some.exit_0
                    (or (<= main@%xs.tr.ph.i18.lcssa_1 0) (> main@%_16_0 0)))
                (=> main@some.exit_0 a!2)
                (=> main@some.exit_0
                    (or (<= main@%xs.tr.ph.i18.lcssa_1 0) (> main@%_17_0 0)))
                (=> main@some.exit_0 (> main@%xs.tr.ph.i18.lcssa_1 0))
                (=> main@some.exit_0
                    (= main@%_18_0 (select main@%_1_0 main@%_17_0)))
                (=> main@some.exit_0
                    (= main@%_19_0 (select main@%_1_0 main@%_16_0)))
                (=> main@some.exit_0 (= main@%_20_0 (+ main@%_19_0 1)))
                (=> main@some.exit_0
                    (= main@%_21_0 (store main@%_1_0 main@%_16_0 main@%_20_0)))
                (=> main@some.exit_0 (= main@%_22_0 (= main@%_18_0 0)))
                (=> main@tailrecurse.i5.preheader_0
                    (and main@tailrecurse.i5.preheader_0 main@some.exit_0))
                (=> (and main@tailrecurse.i5.preheader_0 main@some.exit_0)
                    (not main@%_22_0))
                (=> main@tailrecurse.i5_0
                    (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0))
                main@tailrecurse.i5_0
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%xs.tr.ph.i217_0 main@%_18_0))
                (=> (and main@tailrecurse.i5_0 main@tailrecurse.i5.preheader_0)
                    (= main@%xs.tr.ph.i217_1 main@%xs.tr.ph.i217_0)))))
  (=> a!3
      (main@tailrecurse.i5
        @nd_0
        main@%xs.tr.ph.i217_1
        main@%_21_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_16_0 (+ (+ main@%xs.tr.ph.i18.lcssa_1 (* 0 8)) 0)))
      (a!2 (= main@%_17_0 (+ (+ main@%xs.tr.ph.i18.lcssa_1 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i1
                  @nd_0
                  main@%xs.tr.ph.i18_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@some.exit_0
                    (and main@some.exit_0 main@tailrecurse.i1_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (not main@%_12_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (= main@%xs.tr.ph.i18.lcssa_0 main@%xs.tr.ph.i18_0))
                (=> (and main@some.exit_0 main@tailrecurse.i1_0)
                    (= main@%xs.tr.ph.i18.lcssa_1 main@%xs.tr.ph.i18.lcssa_0))
                (=> main@some.exit_0 a!1)
                (=> main@some.exit_0
                    (or (<= main@%xs.tr.ph.i18.lcssa_1 0) (> main@%_16_0 0)))
                (=> main@some.exit_0 a!2)
                (=> main@some.exit_0
                    (or (<= main@%xs.tr.ph.i18.lcssa_1 0) (> main@%_17_0 0)))
                (=> main@some.exit_0 (> main@%xs.tr.ph.i18.lcssa_1 0))
                (=> main@some.exit_0
                    (= main@%_18_0 (select main@%_1_0 main@%_17_0)))
                (=> main@some.exit_0
                    (= main@%_19_0 (select main@%_1_0 main@%_16_0)))
                (=> main@some.exit_0 (= main@%_20_0 (+ main@%_19_0 1)))
                (=> main@some.exit_0
                    (= main@%_21_0 (store main@%_1_0 main@%_16_0 main@%_20_0)))
                (=> main@some.exit_0 (= main@%_22_0 (= main@%_18_0 0)))
                (=> main@tailrecurse.us.i4.preheader_0
                    (and main@tailrecurse.us.i4.preheader_0 main@some.exit_0))
                (=> (and main@tailrecurse.us.i4.preheader_0 main@some.exit_0)
                    main@%_22_0)
                (=> main@tailrecurse.us.i4_0
                    (and main@tailrecurse.us.i4_0
                         main@tailrecurse.us.i4.preheader_0))
                main@tailrecurse.us.i4_0)))
  (=> a!3 main@tailrecurse.us.i4))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i_0
               (= main@%_13_0 (+ main@%xs.tr.ph.i18_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i1
                  @nd_0
                  main@%xs.tr.ph.i18_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@tailrecurse.outer.i_0
                    (and main@tailrecurse.outer.i_0 main@tailrecurse.i1_0))
                (=> (and main@tailrecurse.outer.i_0 main@tailrecurse.i1_0)
                    main@%_12_0)
                a!1
                (=> main@tailrecurse.outer.i_0
                    (or (<= main@%xs.tr.ph.i18_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.i_0 (> main@%xs.tr.ph.i18_0 0))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_14_0 (select main@%_1_0 main@%_13_0)))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_15_0 (= main@%_14_0 0)))
                (=> main@tailrecurse.us.i.preheader.loopexit_0
                    (and main@tailrecurse.us.i.preheader.loopexit_0
                         main@tailrecurse.outer.i_0))
                (=> (and main@tailrecurse.us.i.preheader.loopexit_0
                         main@tailrecurse.outer.i_0)
                    main@%_15_0)
                (=> main@tailrecurse.us.i.preheader_0
                    (and main@tailrecurse.us.i.preheader_0
                         main@tailrecurse.us.i.preheader.loopexit_0))
                (=> main@tailrecurse.us.i_0
                    (and main@tailrecurse.us.i_0
                         main@tailrecurse.us.i.preheader_0))
                main@tailrecurse.us.i_0)))
  (=> a!2 main@tailrecurse.us.i))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i3_0
               (= main@%_26_0 (+ main@%xs.tr.ph.i217_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i5
                  @nd_0
                  main@%xs.tr.ph.i217_0
                  main@%_21_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_23_0 @nd_0)
                (= main@%_25_0 (= main@%_24_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (and main@tailrecurse.outer.i3_0 main@tailrecurse.i5_0))
                (=> (and main@tailrecurse.outer.i3_0 main@tailrecurse.i5_0)
                    main@%_25_0)
                a!1
                (=> main@tailrecurse.outer.i3_0
                    (or (<= main@%xs.tr.ph.i217_0 0) (> main@%_26_0 0)))
                (=> main@tailrecurse.outer.i3_0 (> main@%xs.tr.ph.i217_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_27_0 (select main@%_21_0 main@%_26_0)))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_28_0 (= main@%_27_0 0)))
                (=> main@tailrecurse.i5_1
                    (and main@tailrecurse.i5_1 main@tailrecurse.outer.i3_0))
                main@tailrecurse.i5_1
                (=> (and main@tailrecurse.i5_1 main@tailrecurse.outer.i3_0)
                    (not main@%_28_0))
                (=> (and main@tailrecurse.i5_1 main@tailrecurse.outer.i3_0)
                    (= main@%xs.tr.ph.i217_1 main@%_27_0))
                (=> (and main@tailrecurse.i5_1 main@tailrecurse.outer.i3_0)
                    (= main@%xs.tr.ph.i217_2 main@%xs.tr.ph.i217_1)))))
  (=> a!2
      (main@tailrecurse.i5
        @nd_0
        main@%xs.tr.ph.i217_2
        main@%_21_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (=> main@tailrecurse.i11.preheader_0
               (= main@%_29_0 (+ main@%xs.tr.ph.i217.lcssa_1 (* 0 8) 0)))))
(let ((a!2 (and (main@tailrecurse.i5
                  @nd_0
                  main@%xs.tr.ph.i217_0
                  main@%_21_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_23_0 @nd_0)
                (= main@%_25_0 (= main@%_24_0 0))
                (=> main@tailrecurse.i11.preheader_0
                    (and main@tailrecurse.i11.preheader_0 main@tailrecurse.i5_0))
                (=> (and main@tailrecurse.i11.preheader_0 main@tailrecurse.i5_0)
                    (not main@%_25_0))
                (=> (and main@tailrecurse.i11.preheader_0 main@tailrecurse.i5_0)
                    (= main@%xs.tr.ph.i217.lcssa_0 main@%xs.tr.ph.i217_0))
                (=> (and main@tailrecurse.i11.preheader_0 main@tailrecurse.i5_0)
                    (= main@%xs.tr.ph.i217.lcssa_1 main@%xs.tr.ph.i217.lcssa_0))
                a!1
                (=> main@tailrecurse.i11.preheader_0
                    (or (<= main@%xs.tr.ph.i217.lcssa_1 0) (> main@%_29_0 0)))
                (=> main@tailrecurse.i11.preheader_0
                    (= main@%_30_0 (select main@%_21_0 main@%_29_0)))
                (=> main@tailrecurse.i11.preheader_0
                    (= main@%_31_0 (+ main@%_30_0 1)))
                (=> main@tailrecurse.i11.preheader_0
                    (= main@%_32_0 (store main@%_21_0 main@%_29_0 main@%_31_0)))
                (=> main@tailrecurse.i11_0
                    (and main@tailrecurse.i11_0
                         main@tailrecurse.i11.preheader_0))
                main@tailrecurse.i11_0
                (=> (and main@tailrecurse.i11_0
                         main@tailrecurse.i11.preheader_0)
                    (= main@%xs.tr2.i9_0 main@%_2_0))
                (=> (and main@tailrecurse.i11_0
                         main@tailrecurse.i11.preheader_0)
                    (= main@%accumulator.tr1.i10_0 0))
                (=> (and main@tailrecurse.i11_0
                         main@tailrecurse.i11.preheader_0)
                    (= main@%xs.tr2.i9_1 main@%xs.tr2.i9_0))
                (=> (and main@tailrecurse.i11_0
                         main@tailrecurse.i11.preheader_0)
                    (= main@%accumulator.tr1.i10_1 main@%accumulator.tr1.i10_0)))))
  (=> a!2
      (main@tailrecurse.i11
        main@%phitmp_0
        main@%xs.tr2.i9_1
        main@%_32_0
        main@%accumulator.tr1.i10_1)))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i3_0
               (= main@%_26_0 (+ main@%xs.tr.ph.i217_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i5
                  @nd_0
                  main@%xs.tr.ph.i217_0
                  main@%_21_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_23_0 @nd_0)
                (= main@%_25_0 (= main@%_24_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (and main@tailrecurse.outer.i3_0 main@tailrecurse.i5_0))
                (=> (and main@tailrecurse.outer.i3_0 main@tailrecurse.i5_0)
                    main@%_25_0)
                a!1
                (=> main@tailrecurse.outer.i3_0
                    (or (<= main@%xs.tr.ph.i217_0 0) (> main@%_26_0 0)))
                (=> main@tailrecurse.outer.i3_0 (> main@%xs.tr.ph.i217_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_27_0 (select main@%_21_0 main@%_26_0)))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_28_0 (= main@%_27_0 0)))
                (=> main@tailrecurse.us.i4.preheader.loopexit_0
                    (and main@tailrecurse.us.i4.preheader.loopexit_0
                         main@tailrecurse.outer.i3_0))
                (=> (and main@tailrecurse.us.i4.preheader.loopexit_0
                         main@tailrecurse.outer.i3_0)
                    main@%_28_0)
                (=> main@tailrecurse.us.i4.preheader_0
                    (and main@tailrecurse.us.i4.preheader_0
                         main@tailrecurse.us.i4.preheader.loopexit_0))
                (=> main@tailrecurse.us.i4_0
                    (and main@tailrecurse.us.i4_0
                         main@tailrecurse.us.i4.preheader_0))
                main@tailrecurse.us.i4_0)))
  (=> a!2 main@tailrecurse.us.i4))))
(rule (let ((a!1 (= main@%_33_0 (+ (+ main@%xs.tr2.i9_0 (* 0 8)) 0)))
      (a!2 (= main@%_35_0 (+ (+ main@%xs.tr2.i9_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i11
             main@%phitmp_0
             main@%xs.tr2.i9_0
             main@%_32_0
             main@%accumulator.tr1.i10_0)
           true
           a!1
           (or (<= main@%xs.tr2.i9_0 0) (> main@%_33_0 0))
           (= main@%_34_0 (select main@%_32_0 main@%_33_0))
           a!2
           (or (<= main@%xs.tr2.i9_0 0) (> main@%_35_0 0))
           (> main@%xs.tr2.i9_0 0)
           (= main@%_36_0 (select main@%_32_0 main@%_35_0))
           (= main@%_37_0 (+ main@%_34_0 main@%accumulator.tr1.i10_0))
           (= main@%_38_0 (= main@%_36_0 0))
           (=> main@tailrecurse.i11_1
               (and main@tailrecurse.i11_1 main@tailrecurse.i11_0))
           main@tailrecurse.i11_1
           (=> (and main@tailrecurse.i11_1 main@tailrecurse.i11_0)
               (not main@%_38_0))
           (=> (and main@tailrecurse.i11_1 main@tailrecurse.i11_0)
               (= main@%xs.tr2.i9_1 main@%_36_0))
           (=> (and main@tailrecurse.i11_1 main@tailrecurse.i11_0)
               (= main@%accumulator.tr1.i10_1 main@%_37_0))
           (=> (and main@tailrecurse.i11_1 main@tailrecurse.i11_0)
               (= main@%xs.tr2.i9_2 main@%xs.tr2.i9_1))
           (=> (and main@tailrecurse.i11_1 main@tailrecurse.i11_0)
               (= main@%accumulator.tr1.i10_2 main@%accumulator.tr1.i10_1)))
      (main@tailrecurse.i11
        main@%phitmp_0
        main@%xs.tr2.i9_2
        main@%_32_0
        main@%accumulator.tr1.i10_2))))
(rule (let ((a!1 (= main@%_33_0 (+ (+ main@%xs.tr2.i9_0 (* 0 8)) 0)))
      (a!2 (= main@%_35_0 (+ (+ main@%xs.tr2.i9_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i11
                  main@%phitmp_0
                  main@%xs.tr2.i9_0
                  main@%_32_0
                  main@%accumulator.tr1.i10_0)
                true
                a!1
                (or (<= main@%xs.tr2.i9_0 0) (> main@%_33_0 0))
                (= main@%_34_0 (select main@%_32_0 main@%_33_0))
                a!2
                (or (<= main@%xs.tr2.i9_0 0) (> main@%_35_0 0))
                (> main@%xs.tr2.i9_0 0)
                (= main@%_36_0 (select main@%_32_0 main@%_35_0))
                (= main@%_37_0 (+ main@%_34_0 main@%accumulator.tr1.i10_0))
                (= main@%_38_0 (= main@%_36_0 0))
                (=> main@sum.exit13_0
                    (and main@sum.exit13_0 main@tailrecurse.i11_0))
                (=> (and main@sum.exit13_0 main@tailrecurse.i11_0) main@%_38_0)
                (=> (and main@sum.exit13_0 main@tailrecurse.i11_0)
                    (= main@%.lcssa_0 main@%_37_0))
                (=> (and main@sum.exit13_0 main@tailrecurse.i11_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@sum.exit13_0
                    (= main@%_39_0 (> main@%.lcssa_1 main@%phitmp_0)))
                (=> main@sum.exit13_0 (not main@%_39_0))
                (=> main@sum.exit13.split_0
                    (and main@sum.exit13.split_0 main@sum.exit13_0))
                main@sum.exit13.split_0)))
  (=> a!3 main@sum.exit13.split))))
(rule (=> (and main@tailrecurse.us.i4
         true
         (=> main@tailrecurse.us.i4_1
             (and main@tailrecurse.us.i4_1 main@tailrecurse.us.i4_0))
         main@tailrecurse.us.i4_1)
    main@tailrecurse.us.i4))
(rule (=> (and main@tailrecurse.us.i
         true
         (=> main@tailrecurse.us.i_1
             (and main@tailrecurse.us.i_1 main@tailrecurse.us.i_0))
         main@tailrecurse.us.i_1)
    main@tailrecurse.us.i))
(query main@sum.exit13.split)

