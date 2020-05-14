(set-info :original "8-lists/lists-4-inc-some2-unsafe.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel nd_list@_1 ((Array Int Int) Int ))
(declare-rel nd_list@UnifiedReturnBlock.split ((Array Int Int) Int (Array Int Int) Int ))
(declare-rel nd_list (Bool Bool Bool (Array Int Int) Int ))
(declare-rel main@entry (Int ))
(declare-rel main@tailrecurse.i (Int (Array Int Int) Int Bool Int Int ))
(declare-rel main@tailrecurse.i1 (Int Int (Array Int Int) Int Int ))
(declare-rel main@tailrecurse.i6 (Int (Array Int Int) Int Int Int Int ))
(declare-rel main@tailrecurse.i13 (Int Int (Array Int Int) Int ))
(declare-rel main@sum.exit15.split ())
(declare-rel main@tailrecurse.us.i5 ())
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
(declare-var main@%.tr1.ph.i2.in_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_35_0 Bool )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%.lcssa_1 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 (Array Int Int) )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%.tr2.i11_2 Int )
(declare-var main@%accumulator.tr1.i12_2 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%.tr1.ph.i223.lcssa_1 Int )
(declare-var main@%.tr1.ph.i2.in21_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%.tr1.ph.i24.lcssa_1 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%.lcssa39_1 Int )
(declare-var main@%.tr2.i_2 Int )
(declare-var main@%accumulator.tr1.i_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 (Array Int Int) )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Bool )
(declare-var main@.lr.ph.i_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%.tr2.i_0 Int )
(declare-var main@%accumulator.tr1.i_0 Int )
(declare-var main@%.tr2.i_1 Int )
(declare-var main@%accumulator.tr1.i_1 Int )
(declare-var main@tailrecurse.outer.split.us.i_0 Bool )
(declare-var main@tailrecurse.us.i_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@sum.exit_0 Bool )
(declare-var main@%.lcssa39_0 Int )
(declare-var main@%phitmp_0 Int )
(declare-var main@tailrecurse.i1.lr.ph_0 Bool )
(declare-var main@tailrecurse.i1_0 Bool )
(declare-var main@%.tr1.ph.i24_0 Int )
(declare-var main@%.tr1.ph.i24_1 Int )
(declare-var main@tailrecurse.outer.i_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@tailrecurse.i1_1 Bool )
(declare-var main@%.tr1.ph.i24_2 Int )
(declare-var main@take_some_rest.exit_0 Bool )
(declare-var main@%.tr1.ph.i24.lcssa_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%.tr1.ph.i222_0 Int )
(declare-var main@tailrecurse.i6.lr.ph_0 Bool )
(declare-var main@tailrecurse.i6_0 Bool )
(declare-var main@%.tr1.ph.i223_0 Int )
(declare-var main@%.tr1.ph.i223_1 Int )
(declare-var main@tailrecurse.outer.split.us.i4_0 Bool )
(declare-var main@tailrecurse.us.i5_0 Bool )
(declare-var main@tailrecurse.outer.split.us.i.loopexit_0 Bool )
(declare-var main@tailrecurse.outer.i3_0 Bool )
(declare-var main@%.tr1.ph.i2_0 Int )
(declare-var main@tailrecurse.i6_1 Bool )
(declare-var main@%.tr1.ph.i223_2 Int )
(declare-var main@.lr.ph.i10_0 Bool )
(declare-var main@%.tr1.ph.i223.lcssa_0 Int )
(declare-var main@%_28_0 (Array Int Int) )
(declare-var main@tailrecurse.i13_0 Bool )
(declare-var main@%.tr2.i11_0 Int )
(declare-var main@%accumulator.tr1.i12_0 Int )
(declare-var main@%.tr2.i11_1 Int )
(declare-var main@%accumulator.tr1.i12_1 Int )
(declare-var main@tailrecurse.outer.split.us.i4.loopexit_0 Bool )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@tailrecurse.i13_1 Bool )
(declare-var main@sum.exit15_0 Bool )
(declare-var main@%.lcssa_0 Int )
(declare-var main@sum.exit15.split_0 Bool )
(declare-var main@tailrecurse.us.i5_1 Bool )
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
         (=> main@.lr.ph.i_0 (and main@.lr.ph.i_0 main@entry_0))
         (=> (and main@.lr.ph.i_0 main@entry_0) (not main@%_3_0))
         (=> main@tailrecurse.i_0 (and main@tailrecurse.i_0 main@.lr.ph.i_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.tr2.i_0 main@%_2_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%accumulator.tr1.i_0 0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%.tr2.i_1 main@%.tr2.i_0))
         (=> (and main@tailrecurse.i_0 main@.lr.ph.i_0)
             (= main@%accumulator.tr1.i_1 main@%accumulator.tr1.i_0)))
    (main@tailrecurse.i
      @nd_0
      main@%_1_0
      main@%_2_0
      main@%_3_0
      main@%.tr2.i_1
      main@%accumulator.tr1.i_1)))
(rule (=> (and (main@entry @nd_0)
         true
         (nd_list true false false main@%_1_0 main@%_2_0)
         (= main@%_3_0 (= main@%_2_0 0))
         (=> main@tailrecurse.outer.split.us.i_0
             (and main@tailrecurse.outer.split.us.i_0 main@entry_0))
         (=> (and main@tailrecurse.outer.split.us.i_0 main@entry_0) main@%_3_0)
         (=> main@tailrecurse.us.i_0
             (and main@tailrecurse.us.i_0 main@tailrecurse.outer.split.us.i_0))
         main@tailrecurse.us.i_0)
    main@tailrecurse.us.i))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i
             @nd_0
             main@%_1_0
             main@%_2_0
             main@%_3_0
             main@%.tr2.i_0
             main@%accumulator.tr1.i_0)
           true
           a!1
           (or (<= main@%.tr2.i_0 0) (> main@%_4_0 0))
           (= main@%_5_0 (select main@%_1_0 main@%_4_0))
           a!2
           (or (<= main@%.tr2.i_0 0) (> main@%_6_0 0))
           (> main@%.tr2.i_0 0)
           (= main@%_7_0 (select main@%_1_0 main@%_6_0))
           (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
           (= main@%_9_0 (= main@%_7_0 0))
           (=> main@tailrecurse.i_1
               (and main@tailrecurse.i_1 main@tailrecurse.i_0))
           main@tailrecurse.i_1
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) (not main@%_9_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr2.i_1 main@%_7_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr1.i_1 main@%_8_0))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%.tr2.i_2 main@%.tr2.i_1))
           (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
               (= main@%accumulator.tr1.i_2 main@%accumulator.tr1.i_1)))
      (main@tailrecurse.i
        @nd_0
        main@%_1_0
        main@%_2_0
        main@%_3_0
        main@%.tr2.i_2
        main@%accumulator.tr1.i_2))))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%_1_0
                  main@%_2_0
                  main@%_3_0
                  main@%.tr2.i_0
                  main@%accumulator.tr1.i_0)
                true
                a!1
                (or (<= main@%.tr2.i_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%_1_0 main@%_4_0))
                a!2
                (or (<= main@%.tr2.i_0 0) (> main@%_6_0 0))
                (> main@%.tr2.i_0 0)
                (= main@%_7_0 (select main@%_1_0 main@%_6_0))
                (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
                (= main@%_9_0 (= main@%_7_0 0))
                (=> main@sum.exit_0 (and main@sum.exit_0 main@tailrecurse.i_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0) main@%_9_0)
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa39_0 main@%_8_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa39_1 main@%.lcssa39_0))
                (=> main@sum.exit_0 (= main@%phitmp_0 (+ main@%.lcssa39_1 2)))
                (=> main@tailrecurse.i1.lr.ph_0
                    (and main@tailrecurse.i1.lr.ph_0 main@sum.exit_0))
                (=> (and main@tailrecurse.i1.lr.ph_0 main@sum.exit_0)
                    (not main@%_3_0))
                (=> main@tailrecurse.i1_0
                    (and main@tailrecurse.i1_0 main@tailrecurse.i1.lr.ph_0))
                main@tailrecurse.i1_0
                (=> (and main@tailrecurse.i1_0 main@tailrecurse.i1.lr.ph_0)
                    (= main@%.tr1.ph.i24_0 main@%_2_0))
                (=> (and main@tailrecurse.i1_0 main@tailrecurse.i1.lr.ph_0)
                    (= main@%.tr1.ph.i24_1 main@%.tr1.ph.i24_0)))))
  (=> a!3
      (main@tailrecurse.i1
        @nd_0
        main@%.tr1.ph.i24_1
        main@%_1_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_4_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 0)))
      (a!2 (= main@%_6_0 (+ (+ main@%.tr2.i_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i
                  @nd_0
                  main@%_1_0
                  main@%_2_0
                  main@%_3_0
                  main@%.tr2.i_0
                  main@%accumulator.tr1.i_0)
                true
                a!1
                (or (<= main@%.tr2.i_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%_1_0 main@%_4_0))
                a!2
                (or (<= main@%.tr2.i_0 0) (> main@%_6_0 0))
                (> main@%.tr2.i_0 0)
                (= main@%_7_0 (select main@%_1_0 main@%_6_0))
                (= main@%_8_0 (+ main@%_5_0 main@%accumulator.tr1.i_0))
                (= main@%_9_0 (= main@%_7_0 0))
                (=> main@sum.exit_0 (and main@sum.exit_0 main@tailrecurse.i_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0) main@%_9_0)
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa39_0 main@%_8_0))
                (=> (and main@sum.exit_0 main@tailrecurse.i_0)
                    (= main@%.lcssa39_1 main@%.lcssa39_0))
                (=> main@sum.exit_0 (= main@%phitmp_0 (+ main@%.lcssa39_1 2)))
                (=> main@tailrecurse.outer.split.us.i_0
                    (and main@tailrecurse.outer.split.us.i_0 main@sum.exit_0))
                (=> (and main@tailrecurse.outer.split.us.i_0 main@sum.exit_0)
                    main@%_3_0)
                (=> main@tailrecurse.us.i_0
                    (and main@tailrecurse.us.i_0
                         main@tailrecurse.outer.split.us.i_0))
                main@tailrecurse.us.i_0)))
  (=> a!3 main@tailrecurse.us.i))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i_0
               (= main@%_13_0 (+ main@%.tr1.ph.i24_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.ph.i24_0
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
                    (or (<= main@%.tr1.ph.i24_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.i_0 (> main@%.tr1.ph.i24_0 0))
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
                    (= main@%.tr1.ph.i24_1 main@%_14_0))
                (=> (and main@tailrecurse.i1_1 main@tailrecurse.outer.i_0)
                    (= main@%.tr1.ph.i24_2 main@%.tr1.ph.i24_1)))))
  (=> a!2
      (main@tailrecurse.i1
        @nd_0
        main@%.tr1.ph.i24_2
        main@%_1_0
        main@%phitmp_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_16_0 (+ (+ main@%.tr1.ph.i24.lcssa_1 (* 0 8)) 0)))
      (a!2 (= main@%.tr1.ph.i2.in21_0
              (+ (+ main@%.tr1.ph.i24.lcssa_1 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.ph.i24_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@take_some_rest.exit_0
                    (and main@take_some_rest.exit_0 main@tailrecurse.i1_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (not main@%_12_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (= main@%.tr1.ph.i24.lcssa_0 main@%.tr1.ph.i24_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (= main@%.tr1.ph.i24.lcssa_1 main@%.tr1.ph.i24.lcssa_0))
                (=> main@take_some_rest.exit_0 a!1)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.ph.i24.lcssa_1 0) (> main@%_16_0 0)))
                (=> main@take_some_rest.exit_0 a!2)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.ph.i24.lcssa_1 0)
                        (> main@%.tr1.ph.i2.in21_0 0)))
                (=> main@take_some_rest.exit_0 (> main@%.tr1.ph.i24.lcssa_1 0))
                (=> main@take_some_rest.exit_0
                    (= main@%.tr1.ph.i222_0
                       (select main@%_1_0 main@%.tr1.ph.i2.in21_0)))
                (=> main@take_some_rest.exit_0
                    (= main@%_17_0 (= main@%.tr1.ph.i222_0 0)))
                (=> main@tailrecurse.i6.lr.ph_0
                    (and main@tailrecurse.i6.lr.ph_0 main@take_some_rest.exit_0))
                (=> (and main@tailrecurse.i6.lr.ph_0 main@take_some_rest.exit_0)
                    (not main@%_17_0))
                (=> main@tailrecurse.i6_0
                    (and main@tailrecurse.i6_0 main@tailrecurse.i6.lr.ph_0))
                main@tailrecurse.i6_0
                (=> (and main@tailrecurse.i6_0 main@tailrecurse.i6.lr.ph_0)
                    (= main@%.tr1.ph.i223_0 main@%.tr1.ph.i222_0))
                (=> (and main@tailrecurse.i6_0 main@tailrecurse.i6.lr.ph_0)
                    (= main@%.tr1.ph.i223_1 main@%.tr1.ph.i223_0)))))
  (=> a!3
      (main@tailrecurse.i6
        @nd_0
        main@%_1_0
        main@%.tr1.ph.i223_1
        main@%phitmp_0
        main@%_16_0
        main@%_2_0)))))
(rule (let ((a!1 (= main@%_16_0 (+ (+ main@%.tr1.ph.i24.lcssa_1 (* 0 8)) 0)))
      (a!2 (= main@%.tr1.ph.i2.in21_0
              (+ (+ main@%.tr1.ph.i24.lcssa_1 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.ph.i24_0
                  main@%_1_0
                  main@%phitmp_0
                  main@%_2_0)
                true
                (= main@%_10_0 @nd_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@take_some_rest.exit_0
                    (and main@take_some_rest.exit_0 main@tailrecurse.i1_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (not main@%_12_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (= main@%.tr1.ph.i24.lcssa_0 main@%.tr1.ph.i24_0))
                (=> (and main@take_some_rest.exit_0 main@tailrecurse.i1_0)
                    (= main@%.tr1.ph.i24.lcssa_1 main@%.tr1.ph.i24.lcssa_0))
                (=> main@take_some_rest.exit_0 a!1)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.ph.i24.lcssa_1 0) (> main@%_16_0 0)))
                (=> main@take_some_rest.exit_0 a!2)
                (=> main@take_some_rest.exit_0
                    (or (<= main@%.tr1.ph.i24.lcssa_1 0)
                        (> main@%.tr1.ph.i2.in21_0 0)))
                (=> main@take_some_rest.exit_0 (> main@%.tr1.ph.i24.lcssa_1 0))
                (=> main@take_some_rest.exit_0
                    (= main@%.tr1.ph.i222_0
                       (select main@%_1_0 main@%.tr1.ph.i2.in21_0)))
                (=> main@take_some_rest.exit_0
                    (= main@%_17_0 (= main@%.tr1.ph.i222_0 0)))
                (=> main@tailrecurse.outer.split.us.i4_0
                    (and main@tailrecurse.outer.split.us.i4_0
                         main@take_some_rest.exit_0))
                (=> (and main@tailrecurse.outer.split.us.i4_0
                         main@take_some_rest.exit_0)
                    main@%_17_0)
                (=> main@tailrecurse.us.i5_0
                    (and main@tailrecurse.us.i5_0
                         main@tailrecurse.outer.split.us.i4_0))
                main@tailrecurse.us.i5_0)))
  (=> a!3 main@tailrecurse.us.i5))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i_0
               (= main@%_13_0 (+ main@%.tr1.ph.i24_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i1
                  @nd_0
                  main@%.tr1.ph.i24_0
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
                    (or (<= main@%.tr1.ph.i24_0 0) (> main@%_13_0 0)))
                (=> main@tailrecurse.outer.i_0 (> main@%.tr1.ph.i24_0 0))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_14_0 (select main@%_1_0 main@%_13_0)))
                (=> main@tailrecurse.outer.i_0
                    (= main@%_15_0 (= main@%_14_0 0)))
                (=> main@tailrecurse.outer.split.us.i.loopexit_0
                    (and main@tailrecurse.outer.split.us.i.loopexit_0
                         main@tailrecurse.outer.i_0))
                (=> (and main@tailrecurse.outer.split.us.i.loopexit_0
                         main@tailrecurse.outer.i_0)
                    main@%_15_0)
                (=> main@tailrecurse.outer.split.us.i_0
                    (and main@tailrecurse.outer.split.us.i_0
                         main@tailrecurse.outer.split.us.i.loopexit_0))
                (=> main@tailrecurse.us.i_0
                    (and main@tailrecurse.us.i_0
                         main@tailrecurse.outer.split.us.i_0))
                main@tailrecurse.us.i_0)))
  (=> a!2 main@tailrecurse.us.i))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i3_0
               (= main@%.tr1.ph.i2.in_0 (+ main@%.tr1.ph.i223_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i6
                  @nd_0
                  main@%_1_0
                  main@%.tr1.ph.i223_0
                  main@%phitmp_0
                  main@%_16_0
                  main@%_2_0)
                true
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (and main@tailrecurse.outer.i3_0 main@tailrecurse.i6_0))
                (=> (and main@tailrecurse.outer.i3_0 main@tailrecurse.i6_0)
                    main@%_21_0)
                a!1
                (=> main@tailrecurse.outer.i3_0
                    (or (<= main@%.tr1.ph.i223_0 0) (> main@%.tr1.ph.i2.in_0 0)))
                (=> main@tailrecurse.outer.i3_0 (> main@%.tr1.ph.i223_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%.tr1.ph.i2_0
                       (select main@%_1_0 main@%.tr1.ph.i2.in_0)))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_18_0 (= main@%.tr1.ph.i2_0 0)))
                (=> main@tailrecurse.i6_1
                    (and main@tailrecurse.i6_1 main@tailrecurse.outer.i3_0))
                main@tailrecurse.i6_1
                (=> (and main@tailrecurse.i6_1 main@tailrecurse.outer.i3_0)
                    (not main@%_18_0))
                (=> (and main@tailrecurse.i6_1 main@tailrecurse.outer.i3_0)
                    (= main@%.tr1.ph.i223_1 main@%.tr1.ph.i2_0))
                (=> (and main@tailrecurse.i6_1 main@tailrecurse.outer.i3_0)
                    (= main@%.tr1.ph.i223_2 main@%.tr1.ph.i223_1)))))
  (=> a!2
      (main@tailrecurse.i6
        @nd_0
        main@%_1_0
        main@%.tr1.ph.i223_2
        main@%phitmp_0
        main@%_16_0
        main@%_2_0)))))
(rule (let ((a!1 (=> main@.lr.ph.i10_0
               (= main@%_22_0 (+ main@%.tr1.ph.i223.lcssa_1 (* 0 8) 0)))))
(let ((a!2 (and (main@tailrecurse.i6
                  @nd_0
                  main@%_1_0
                  main@%.tr1.ph.i223_0
                  main@%phitmp_0
                  main@%_16_0
                  main@%_2_0)
                true
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@.lr.ph.i10_0
                    (and main@.lr.ph.i10_0 main@tailrecurse.i6_0))
                (=> (and main@.lr.ph.i10_0 main@tailrecurse.i6_0)
                    (not main@%_21_0))
                (=> (and main@.lr.ph.i10_0 main@tailrecurse.i6_0)
                    (= main@%.tr1.ph.i223.lcssa_0 main@%.tr1.ph.i223_0))
                (=> (and main@.lr.ph.i10_0 main@tailrecurse.i6_0)
                    (= main@%.tr1.ph.i223.lcssa_1 main@%.tr1.ph.i223.lcssa_0))
                a!1
                (=> main@.lr.ph.i10_0
                    (or (<= main@%.tr1.ph.i223.lcssa_1 0) (> main@%_22_0 0)))
                (=> main@.lr.ph.i10_0
                    (= main@%_23_0 (select main@%_1_0 main@%_16_0)))
                (=> main@.lr.ph.i10_0 (= main@%_24_0 (+ main@%_23_0 1)))
                (=> main@.lr.ph.i10_0
                    (= main@%_25_0 (store main@%_1_0 main@%_16_0 main@%_24_0)))
                (=> main@.lr.ph.i10_0
                    (= main@%_26_0 (select main@%_25_0 main@%_22_0)))
                (=> main@.lr.ph.i10_0 (= main@%_27_0 (+ main@%_26_0 1)))
                (=> main@.lr.ph.i10_0
                    (= main@%_28_0 (store main@%_25_0 main@%_22_0 main@%_27_0)))
                (=> main@tailrecurse.i13_0
                    (and main@tailrecurse.i13_0 main@.lr.ph.i10_0))
                main@tailrecurse.i13_0
                (=> (and main@tailrecurse.i13_0 main@.lr.ph.i10_0)
                    (= main@%.tr2.i11_0 main@%_2_0))
                (=> (and main@tailrecurse.i13_0 main@.lr.ph.i10_0)
                    (= main@%accumulator.tr1.i12_0 0))
                (=> (and main@tailrecurse.i13_0 main@.lr.ph.i10_0)
                    (= main@%.tr2.i11_1 main@%.tr2.i11_0))
                (=> (and main@tailrecurse.i13_0 main@.lr.ph.i10_0)
                    (= main@%accumulator.tr1.i12_1 main@%accumulator.tr1.i12_0)))))
  (=> a!2
      (main@tailrecurse.i13
        main@%phitmp_0
        main@%.tr2.i11_1
        main@%_28_0
        main@%accumulator.tr1.i12_1)))))
(rule (let ((a!1 (=> main@tailrecurse.outer.i3_0
               (= main@%.tr1.ph.i2.in_0 (+ main@%.tr1.ph.i223_0 (* 0 8) 4)))))
(let ((a!2 (and (main@tailrecurse.i6
                  @nd_0
                  main@%_1_0
                  main@%.tr1.ph.i223_0
                  main@%phitmp_0
                  main@%_16_0
                  main@%_2_0)
                true
                (= main@%_19_0 @nd_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (and main@tailrecurse.outer.i3_0 main@tailrecurse.i6_0))
                (=> (and main@tailrecurse.outer.i3_0 main@tailrecurse.i6_0)
                    main@%_21_0)
                a!1
                (=> main@tailrecurse.outer.i3_0
                    (or (<= main@%.tr1.ph.i223_0 0) (> main@%.tr1.ph.i2.in_0 0)))
                (=> main@tailrecurse.outer.i3_0 (> main@%.tr1.ph.i223_0 0))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%.tr1.ph.i2_0
                       (select main@%_1_0 main@%.tr1.ph.i2.in_0)))
                (=> main@tailrecurse.outer.i3_0
                    (= main@%_18_0 (= main@%.tr1.ph.i2_0 0)))
                (=> main@tailrecurse.outer.split.us.i4.loopexit_0
                    (and main@tailrecurse.outer.split.us.i4.loopexit_0
                         main@tailrecurse.outer.i3_0))
                (=> (and main@tailrecurse.outer.split.us.i4.loopexit_0
                         main@tailrecurse.outer.i3_0)
                    main@%_18_0)
                (=> main@tailrecurse.outer.split.us.i4_0
                    (and main@tailrecurse.outer.split.us.i4_0
                         main@tailrecurse.outer.split.us.i4.loopexit_0))
                (=> main@tailrecurse.us.i5_0
                    (and main@tailrecurse.us.i5_0
                         main@tailrecurse.outer.split.us.i4_0))
                main@tailrecurse.us.i5_0)))
  (=> a!2 main@tailrecurse.us.i5))))
(rule (let ((a!1 (= main@%_29_0 (+ (+ main@%.tr2.i11_0 (* 0 8)) 0)))
      (a!2 (= main@%_31_0 (+ (+ main@%.tr2.i11_0 (* 0 8)) 4))))
  (=> (and (main@tailrecurse.i13
             main@%phitmp_0
             main@%.tr2.i11_0
             main@%_28_0
             main@%accumulator.tr1.i12_0)
           true
           a!1
           (or (<= main@%.tr2.i11_0 0) (> main@%_29_0 0))
           (= main@%_30_0 (select main@%_28_0 main@%_29_0))
           a!2
           (or (<= main@%.tr2.i11_0 0) (> main@%_31_0 0))
           (> main@%.tr2.i11_0 0)
           (= main@%_32_0 (select main@%_28_0 main@%_31_0))
           (= main@%_33_0 (+ main@%_30_0 main@%accumulator.tr1.i12_0))
           (= main@%_34_0 (= main@%_32_0 0))
           (=> main@tailrecurse.i13_1
               (and main@tailrecurse.i13_1 main@tailrecurse.i13_0))
           main@tailrecurse.i13_1
           (=> (and main@tailrecurse.i13_1 main@tailrecurse.i13_0)
               (not main@%_34_0))
           (=> (and main@tailrecurse.i13_1 main@tailrecurse.i13_0)
               (= main@%.tr2.i11_1 main@%_32_0))
           (=> (and main@tailrecurse.i13_1 main@tailrecurse.i13_0)
               (= main@%accumulator.tr1.i12_1 main@%_33_0))
           (=> (and main@tailrecurse.i13_1 main@tailrecurse.i13_0)
               (= main@%.tr2.i11_2 main@%.tr2.i11_1))
           (=> (and main@tailrecurse.i13_1 main@tailrecurse.i13_0)
               (= main@%accumulator.tr1.i12_2 main@%accumulator.tr1.i12_1)))
      (main@tailrecurse.i13
        main@%phitmp_0
        main@%.tr2.i11_2
        main@%_28_0
        main@%accumulator.tr1.i12_2))))
(rule (let ((a!1 (= main@%_29_0 (+ (+ main@%.tr2.i11_0 (* 0 8)) 0)))
      (a!2 (= main@%_31_0 (+ (+ main@%.tr2.i11_0 (* 0 8)) 4))))
(let ((a!3 (and (main@tailrecurse.i13
                  main@%phitmp_0
                  main@%.tr2.i11_0
                  main@%_28_0
                  main@%accumulator.tr1.i12_0)
                true
                a!1
                (or (<= main@%.tr2.i11_0 0) (> main@%_29_0 0))
                (= main@%_30_0 (select main@%_28_0 main@%_29_0))
                a!2
                (or (<= main@%.tr2.i11_0 0) (> main@%_31_0 0))
                (> main@%.tr2.i11_0 0)
                (= main@%_32_0 (select main@%_28_0 main@%_31_0))
                (= main@%_33_0 (+ main@%_30_0 main@%accumulator.tr1.i12_0))
                (= main@%_34_0 (= main@%_32_0 0))
                (=> main@sum.exit15_0
                    (and main@sum.exit15_0 main@tailrecurse.i13_0))
                (=> (and main@sum.exit15_0 main@tailrecurse.i13_0) main@%_34_0)
                (=> (and main@sum.exit15_0 main@tailrecurse.i13_0)
                    (= main@%.lcssa_0 main@%_33_0))
                (=> (and main@sum.exit15_0 main@tailrecurse.i13_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@sum.exit15_0
                    (= main@%_35_0 (> main@%.lcssa_1 main@%phitmp_0)))
                (=> main@sum.exit15_0 (not main@%_35_0))
                (=> main@sum.exit15.split_0
                    (and main@sum.exit15.split_0 main@sum.exit15_0))
                main@sum.exit15.split_0)))
  (=> a!3 main@sum.exit15.split))))
(rule (=> (and main@tailrecurse.us.i5
         true
         (=> main@tailrecurse.us.i5_1
             (and main@tailrecurse.us.i5_1 main@tailrecurse.us.i5_0))
         main@tailrecurse.us.i5_1)
    main@tailrecurse.us.i5))
(rule (=> (and main@tailrecurse.us.i
         true
         (=> main@tailrecurse.us.i_1
             (and main@tailrecurse.us.i_1 main@tailrecurse.us.i_0))
         main@tailrecurse.us.i_1)
    main@tailrecurse.us.i))
(query main@sum.exit15.split)

