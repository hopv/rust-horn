(set-logic HORN)

(declare-fun %id (Int Int) Bool)
(declare-fun %id.0 (Int Int Int) Bool)
(declare-fun %id.3 (Int Int Bool Int) Bool)
(declare-fun %id2 (Int Int) Bool)
(declare-fun %id2.0 (Int Int Int) Bool)
(declare-fun %id2.3 (Int Int Bool Int) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)

; %id
(assert (forall ((_1 Int) (_@ Int)) (=>
  (and (%id.0 _1 _1 _@))
  (%id _1 _@))))
; %id bb0
(assert (forall ((_1 Int) (_@ Int)) (=>
  (and (= _@ 0))
  (%id.0 _1 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_@ Int) (_@.2 Int)) (=>
  (and (%id2 (- _1 1) _@.2) (distinct _2 0) (%id.3 _1 (+ _@.2 1) (> (+ _@.2 1) 2) _@))
  (%id.0 _1 _2 _@))))
; %id bb3
(assert (forall ((_1 Int) (_3 Int) (_@ Int)) (=>
  (and (= _@ _3))
  (%id.3 _1 _3 false _@))))
(assert (forall ((_1 Int) (_3 Int) (_@ Int)) (=>
  (and (= _@ 2))
  (%id.3 _1 _3 true _@))))

; %id2
(assert (forall ((_1 Int) (_@ Int)) (=>
  (and (%id2.0 _1 _1 _@))
  (%id2 _1 _@))))
; %id2 bb0
(assert (forall ((_1 Int) (_@ Int)) (=>
  (and (= _@ 0))
  (%id2.0 _1 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_@ Int) (_@.2 Int)) (=>
  (and (%id (- _1 1) _@.2) (distinct _2 0) (%id2.3 _1 (+ _@.2 1) (> (+ _@.2 1) 2) _@))
  (%id2.0 _1 _2 _@))))
; %id2 bb3
(assert (forall ((_1 Int) (_3 Int) (_@ Int)) (=>
  (and (= _@ _3))
  (%id2.3 _1 _3 false _@))))
(assert (forall ((_1 Int) (_3 Int) (_@ Int)) (=>
  (and (= _@ 2))
  (%id2.3 _1 _3 true _@))))

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_?.0 Int)) (=>
  (and (%id _?.0 _@.1) (%main.2 _?.0 _@.1 (not (= _@.1 3)) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.2 _1 _2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
