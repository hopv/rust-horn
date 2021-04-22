(set-info :original "03-prusti/prusti-7-pass-mut_borrows-restore.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%SwitchLeaf5.i_0 Bool )
(declare-var main@%SwitchLeaf7.i_0 Bool )
(declare-var main@%Pivot9.i_0 Bool )
(declare-var main@%SwitchLeaf.i_0 Bool )
(declare-var main@%SwitchLeaf2.i_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%.sroa.08.i_0 Int )
(declare-var main@%.sroa.0.i_0 Int )
(declare-var main@%.sroa.08.i.0.sroa_cast2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%.sroa.0.i.0.sroa_cast1_0 Int )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%_0_0 Int )
(declare-var @nd_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var main@%..v.i_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%.sroa.08.i.0..sroa.08.i.0..sroa.08.0..sroa.08.0..i_0 Int )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%Pivot.i_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@%.sroa.0.i.0..sroa.0.i.0..sroa.0.0..sroa.0.0..i_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@LeafBlock1.i_0 Bool )
(declare-var main@LeafBlock.i_0 Bool )
(declare-var main@_7_0 Bool )
(declare-var |tuple(main@LeafBlock.i_0, main@_7_0)| Bool )
(declare-var |tuple(main@LeafBlock1.i_0, main@_7_0)| Bool )
(declare-var main@LeafBlock6.i_0 Bool )
(declare-var main@LeafBlock4.i_0 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@LeafBlock1.i_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@LeafBlock.i_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @nd_0))
(rule (let ((a!1 (and (main@entry @nd_0)
                true
                (> main@%.sroa.08.i_0 0)
                (> main@%.sroa.0.i_0 0)
                (= main@%.sroa.08.i.0.sroa_cast2_0 main@%.sroa.08.i_0)
                (= main@%sm_0 (store main@%sm5_0 main@%.sroa.08.i_0 11))
                (= main@%.sroa.0.i.0.sroa_cast1_0 main@%.sroa.0.i_0)
                (= main@%sm1_0 (store main@%sm_0 main@%.sroa.0.i_0 22))
                (= main@%_0_0 @nd_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (= main@%..v.i_0
                   (ite main@%_2_0 main@%.sroa.0.i_0 main@%.sroa.08.i_0))
                (= main@%_3_0 (select main@%sm1_0 main@%..v.i_0))
                (= main@%_4_0 (+ main@%_3_0 33))
                (= main@%sm2_0 (store main@%sm1_0 main@%..v.i_0 main@%_4_0))
                (= main@%.sroa.08.i.0..sroa.08.i.0..sroa.08.0..sroa.08.0..i_0
                   (select main@%sm2_0 main@%.sroa.08.i_0))
                (= main@%_5_0
                   (+ main@%.sroa.08.i.0..sroa.08.i.0..sroa.08.0..sroa.08.0..i_0
                      44))
                (= main@%sm3_0
                   (store main@%sm2_0 main@%.sroa.08.i_0 main@%_5_0))
                (= main@%.sroa.0.i.0..sroa.0.i.0..sroa.0.0..sroa.0.0..i_0
                   (select main@%sm2_0 main@%.sroa.0.i_0))
                (= main@%_6_0
                   (+ main@%.sroa.0.i.0..sroa.0.i.0..sroa.0.0..sroa.0.0..i_0 44))
                (= main@%sm4_0 (store main@%sm3_0 main@%.sroa.0.i_0 main@%_6_0))
                (= main@%Pivot.i_0
                   (< main@%.sroa.08.i.0..sroa.08.i.0..sroa.08.0..sroa.08.0..i_0
                      44))
                (=> main@LeafBlock1.i_0 (and main@LeafBlock1.i_0 main@entry_0))
                (=> (and main@LeafBlock1.i_0 main@entry_0)
                    (not main@%Pivot.i_0))
                (=> main@LeafBlock1.i_0
                    (= main@%SwitchLeaf2.i_0 (= main@%_5_0 88)))
                (=> main@LeafBlock.i_0 (and main@LeafBlock.i_0 main@entry_0))
                (=> (and main@LeafBlock.i_0 main@entry_0) main@%Pivot.i_0)
                (=> main@LeafBlock.i_0
                    (= main@%SwitchLeaf.i_0 (= main@%_5_0 55)))
                (=> |tuple(main@LeafBlock.i_0, main@_7_0)| main@LeafBlock.i_0)
                (=> |tuple(main@LeafBlock1.i_0, main@_7_0)| main@LeafBlock1.i_0)
                (=> main@_7_0
                    (or |tuple(main@LeafBlock.i_0, main@_7_0)|
                        |tuple(main@LeafBlock1.i_0, main@_7_0)|))
                (=> |tuple(main@LeafBlock.i_0, main@_7_0)| main@%SwitchLeaf.i_0)
                (=> |tuple(main@LeafBlock1.i_0, main@_7_0)|
                    main@%SwitchLeaf2.i_0)
                (=> main@_7_0
                    (= main@%Pivot9.i_0
                       (< main@%.sroa.0.i.0..sroa.0.i.0..sroa.0.0..sroa.0.0..i_0
                          55)))
                (=> main@LeafBlock6.i_0 (and main@LeafBlock6.i_0 main@_7_0))
                (=> (and main@LeafBlock6.i_0 main@_7_0) (not main@%Pivot9.i_0))
                (=> main@LeafBlock6.i_0
                    (= main@%SwitchLeaf7.i_0 (= main@%_6_0 99)))
                (=> main@LeafBlock6.i_0 (not main@%SwitchLeaf7.i_0))
                (=> main@LeafBlock4.i_0 (and main@LeafBlock4.i_0 main@_7_0))
                (=> (and main@LeafBlock4.i_0 main@_7_0) main@%Pivot9.i_0)
                (=> main@LeafBlock4.i_0
                    (= main@%SwitchLeaf5.i_0 (= main@%_6_0 66)))
                (=> main@LeafBlock4.i_0 (not main@%SwitchLeaf5.i_0))
                (=> |tuple(main@LeafBlock1.i_0, main@verifier.error_0)|
                    main@LeafBlock1.i_0)
                (=> |tuple(main@LeafBlock.i_0, main@verifier.error_0)|
                    main@LeafBlock.i_0)
                (=> main@verifier.error_0
                    (or (and main@verifier.error_0 main@LeafBlock6.i_0)
                        (and main@verifier.error_0 main@LeafBlock4.i_0)
                        |tuple(main@LeafBlock1.i_0, main@verifier.error_0)|
                        |tuple(main@LeafBlock.i_0, main@verifier.error_0)|))
                (=> |tuple(main@LeafBlock1.i_0, main@verifier.error_0)|
                    (not main@%SwitchLeaf2.i_0))
                (=> |tuple(main@LeafBlock.i_0, main@verifier.error_0)|
                    (not main@%SwitchLeaf.i_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

