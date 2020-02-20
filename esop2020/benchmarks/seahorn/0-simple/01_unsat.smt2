(set-info :original "0-simple/01_unsat.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph (Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%factor.lcssa_1 Int )
(declare-var main@%x.0.i1_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var @unknown1_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%x.0.i1_0 Int )
(declare-var main@%x.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%x.0.i.lcssa_0 Bool )
(declare-var main@%x.0.i.lcssa_1 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%factor_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%factor.lcssa_0 Int )
(declare-var main@%phitmp_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @unknown1_0))
(rule (=> (and (main@entry @unknown1_0)
         true
         (= main@%_0_0 @unknown1_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@.lr.ph.preheader_0 (and main@.lr.ph.preheader_0 main@entry_0))
         (=> (and main@.lr.ph.preheader_0 main@entry_0) (not main@%_2_0))
         (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
         main@.lr.ph_0
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0) (= main@%x.0.i1_0 1))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%x.0.i1_1 main@%x.0.i1_0)))
    (main@.lr.ph main@%x.0.i1_1 @unknown1_0)))
(rule (=> (and (main@entry @unknown1_0)
         true
         (= main@%_0_0 @unknown1_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@entry_0))
         (=> (and main@verifier.error_0 main@entry_0) main@%_2_0)
         (=> (and main@verifier.error_0 main@entry_0)
             (= main@%x.0.i.lcssa_0 true))
         (=> (and main@verifier.error_0 main@entry_0)
             (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
         (=> main@verifier.error_0 (not main@%x.0.i.lcssa_1))
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(rule (=> (and (main@.lr.ph main@%x.0.i1_0 @unknown1_0)
         true
         (= main@%factor_0 (* main@%x.0.i1_0 2))
         (= main@%_3_0 @unknown1_0)
         (= main@%_5_0 (= main@%_4_0 0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         main@.lr.ph_1
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (not main@%_5_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%x.0.i1_1 main@%factor_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%x.0.i1_2 main@%x.0.i1_1)))
    (main@.lr.ph main@%x.0.i1_2 @unknown1_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%x.0.i1_0 @unknown1_0)
                true
                (= main@%factor_0 (* main@%x.0.i1_0 2))
                (= main@%_3_0 @unknown1_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.lr.ph_0))
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    main@%_5_0)
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    (= main@%factor.lcssa_0 main@%factor_0))
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    (= main@%factor.lcssa_1 main@%factor.lcssa_0))
                (=> main@verifier.error.loopexit_0
                    (= main@%phitmp_0 (> main@%factor.lcssa_1 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_0 main@%phitmp_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
                (=> main@verifier.error_0 (not main@%x.0.i.lcssa_1))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

