(set-info :original "01-simple/simple-4-06_loop_unsat.bc")
(set-info :authors "SeaHorn v.10.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@.lr.ph (Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_7_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var main@%.0.i2_2 Int )
(declare-var main@%.01.i1_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0.i2_0 Int )
(declare-var main@%.01.i1_0 Int )
(declare-var main@%.0.i2_1 Int )
(declare-var main@%.01.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@.lr.ph_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (= main@%_0_0 (= main@%loop.bound_0 0))
         main@%_0_0
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
         (=> (and main@.lr.ph_0 main@entry_0) (not main@%_2_0))
         (=> (and main@.lr.ph_0 main@entry_0) (= main@%.0.i2_0 0))
         (=> (and main@.lr.ph_0 main@entry_0) (= main@%.01.i1_0 1))
         (=> (and main@.lr.ph_0 main@entry_0) (= main@%.0.i2_1 main@%.0.i2_0))
         (=> (and main@.lr.ph_0 main@entry_0) (= main@%.01.i1_1 main@%.01.i1_0))
         main@.lr.ph_0)
    (main@.lr.ph main@%.0.i2_1 main@%.01.i1_1 main@%loop.bound_0)))
(rule (let ((a!1 (and main@entry
                true
                (= main@%_0_0 (= main@%loop.bound_0 0))
                main@%_0_0
                (= main@%_2_0 (= main@%_1_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_2_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 1))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_7_0 (< main@%.01.i.lcssa_1 main@%.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_7_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph main@%.0.i2_0 main@%.01.i1_0 main@%loop.bound_0)
         true
         (= main@%_3_0 (+ main@%.0.i2_0 main@%.01.i1_0))
         (= main@%_4_0 (+ main@%.0.i2_0 1))
         (= main@%_6_0 (= main@%_5_0 main@%loop.bound_0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (not main@%_6_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i2_1 main@%_4_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.01.i1_1 main@%_3_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i2_2 main@%.0.i2_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.01.i1_2 main@%.01.i1_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%.0.i2_2 main@%.01.i1_2 main@%loop.bound_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%.0.i2_0 main@%.01.i1_0 main@%loop.bound_0)
                true
                (= main@%_3_0 (+ main@%.0.i2_0 main@%.01.i1_0))
                (= main@%_4_0 (+ main@%.0.i2_0 1))
                (= main@%_6_0 (= main@%_5_0 main@%loop.bound_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0) main@%_6_0)
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.01.i.lcssa_0 main@%_3_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.0.i.lcssa_0 main@%_4_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_7_0 (< main@%.01.i.lcssa_1 main@%.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_7_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

