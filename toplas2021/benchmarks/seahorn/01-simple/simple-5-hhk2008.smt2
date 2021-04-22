(set-info :original "01-simple/simple-5-hhk2008.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@.lr.ph (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%.02.i2_2 Int )
(declare-var main@%.03.i1_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.02.i2_0 Int )
(declare-var main@%.03.i1_0 Int )
(declare-var main@%.02.i2_1 Int )
(declare-var main@%.03.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.03.i.lcssa_0 Int )
(declare-var main@%.03.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@.lr.ph_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (let ((a!1 (and main@entry
                true
                (= main@%_0_0 (= main@%loop.bound_0 1))
                main@%_0_0
                (= main@%_3_0 (< main@%_1_0 1000001))
                (= main@%_4_0
                   (ite (>= main@%_2_0 0) (< main@%_2_0 1000001) false))
                (= main@%or.cond.i_0 (and main@%_3_0 main@%_4_0))
                main@%or.cond.i_0
                (= main@%_5_0 (> main@%_2_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) main@%_5_0)
                (=> (and main@.lr.ph_0 main@entry_0)
                    (= main@%.02.i2_0 main@%_2_0))
                (=> (and main@.lr.ph_0 main@entry_0)
                    (= main@%.03.i1_0 main@%_1_0))
                (=> (and main@.lr.ph_0 main@entry_0)
                    (= main@%.02.i2_1 main@%.02.i2_0))
                (=> (and main@.lr.ph_0 main@entry_0)
                    (= main@%.03.i1_1 main@%.03.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%_2_0
                   main@%_1_0
                   main@%.02.i2_1
                   main@%.03.i1_1
                   main@%loop.bound_0))))
(rule (let ((a!1 (and main@entry
                true
                (= main@%_0_0 (= main@%loop.bound_0 1))
                main@%_0_0
                (= main@%_3_0 (< main@%_1_0 1000001))
                (= main@%_4_0
                   (ite (>= main@%_2_0 0) (< main@%_2_0 1000001) false))
                (= main@%or.cond.i_0 (and main@%_3_0 main@%_4_0))
                main@%or.cond.i_0
                (= main@%_5_0 (> main@%_2_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) (not main@%_5_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 main@%_1_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_9_0 (+ main@%_2_0 main@%_1_0)))
                (=> main@verifier.error_0
                    (= main@%_10_0 (= main@%.03.i.lcssa_1 main@%_9_0)))
                (=> main@verifier.error_0 (not main@%_10_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph main@%_2_0
                      main@%_1_0
                      main@%.02.i2_0
                      main@%.03.i1_0
                      main@%loop.bound_0)
         true
         (= main@%_6_0 (+ main@%.02.i2_0 (- 1)))
         (= main@%_7_0 (+ main@%.03.i1_0 1))
         (= main@%_8_0 (> main@%.02.i2_0 main@%loop.bound_0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_8_0)
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.02.i2_1 main@%_6_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.03.i1_1 main@%_7_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.02.i2_2 main@%.02.i2_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.03.i1_2 main@%.03.i1_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%_2_0
                 main@%_1_0
                 main@%.02.i2_2
                 main@%.03.i1_2
                 main@%loop.bound_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%_2_0
                             main@%_1_0
                             main@%.02.i2_0
                             main@%.03.i1_0
                             main@%loop.bound_0)
                true
                (= main@%_6_0 (+ main@%.02.i2_0 (- 1)))
                (= main@%_7_0 (+ main@%.03.i1_0 1))
                (= main@%_8_0 (> main@%.02.i2_0 main@%loop.bound_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0) (not main@%_8_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.03.i.lcssa_0 main@%_7_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_9_0 (+ main@%_2_0 main@%_1_0)))
                (=> main@verifier.error_0
                    (= main@%_10_0 (= main@%.03.i.lcssa_1 main@%_9_0)))
                (=> main@verifier.error_0 (not main@%_10_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

