(set-logic HORN)

(declare-fun %ack (Int Int Int) Bool)
(declare-fun %ack.0 (Int Int Int Int) Bool)
(declare-fun %ack.2 (Int Int Int Int) Bool)
(declare-fun %ack1 (Int Int Int) Bool)
(declare-fun %ack1.0 (Int Int Int Int) Bool)
(declare-fun %ack1.2 (Int Int Int Int) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)
(declare-fun %main.5 (Int Int Bool Bool Bool) Bool)
(declare-fun %main.6 (Int Int Bool Bool) Bool)
(declare-fun %main.10 (Int Int Bool Bool Bool) Bool)

; %ack
(assert (forall ((_1 Int) (_2 Int) (_@ Int)) (=>
  (and (%ack.0 _1 _2 _1 _@))
  (%ack _1 _2 _@))))
; %ack bb0
(assert (forall ((_1 Int) (_2 Int) (_@ Int)) (=>
  (and (= _@ (+ _2 1)))
  (%ack.0 _1 _2 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_@ Int)) (=>
  (and (distinct _3 0) (%ack.2 _1 _2 _2 _@))
  (%ack.0 _1 _2 _3 _@))))
; %ack bb2
(assert (forall ((_1 Int) (_2 Int) (_@ Int) (_@.3 Int)) (=>
  (and (%ack (- _1 1) 1 _@.3) (= _@ _@.3))
  (%ack.2 _1 _2 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_5 Int) (_@ Int) (_@.4 Int) (_@.6 Int)) (=>
  (and (%ack _1 (- _2 1) _@.4) (%ack (- _1 1) _@.4 _@.6) (distinct _5 0) (= _@ _@.6))
  (%ack.2 _1 _2 _5 _@))))

; %ack1
(assert (forall ((_1 Int) (_2 Int) (_@ Int)) (=>
  (and (%ack1.0 _1 _2 _1 _@))
  (%ack1 _1 _2 _@))))
; %ack1 bb0
(assert (forall ((_1 Int) (_2 Int) (_@ Int)) (=>
  (and (= _@ (+ _2 1)))
  (%ack1.0 _1 _2 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_@ Int)) (=>
  (and (distinct _3 0) (%ack1.2 _1 _2 _2 _@))
  (%ack1.0 _1 _2 _3 _@))))
; %ack1 bb2
(assert (forall ((_1 Int) (_2 Int) (_@ Int) (_@.3 Int)) (=>
  (and (%ack1 (- _1 1) 1 _@.3) (= _@ _@.3))
  (%ack1.2 _1 _2 0 _@))))
(assert (forall ((_1 Int) (_2 Int) (_5 Int) (_@ Int) (_@.4 Int) (_@.6 Int)) (=>
  (and (%ack1 _1 (- _2 1) _@.4) (%ack1 (- _1 1) _@.4 _@.6) (distinct _5 0) (= _@ _@.6))
  (%ack1.2 _1 _2 _5 _@))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int)) (=>
  (and (%main.2 _?.0 _?.1 (<= 0 _?.0) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.6 _1 _2 false _!))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.5 _1 _2 true (<= 0 _2) _!))
  (%main.2 _1 _2 true _!))))
; %main bb5
(assert (forall ((_1 Int) (_2 Int) (_4 Bool) (_! Bool)) (=>
  (and (%main.6 _1 _2 false _!))
  (%main.5 _1 _2 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_4 Bool) (_! Bool)) (=>
  (and (%main.6 _1 _2 true _!))
  (%main.5 _1 _2 _4 true _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.6 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_@.7 Int) (_@.9 Int)) (=>
  (and (%ack _1 _2 _@.7) (%ack1 _1 _2 _@.9) (%main.10 _1 _2 true (not (= _@.7 _@.9)) _!))
  (%main.6 _1 _2 true _!))))
; %main bb10
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool)) (=>
  (and (= _! false))
  (%main.10 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool)) (=>
  (and (= _! true))
  (%main.10 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
