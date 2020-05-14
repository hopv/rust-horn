(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)
(declare-fun %main.3 (Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Bool Bool Bool) Bool)
(declare-fun %main.8 (Int Int Bool Bool) Bool)
(declare-fun %main.11 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.12 (Int Int Int Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int)) (=>
  (and (%main.2 _?.0 _?.1 (not (<= _?.0 1000000)) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.3 _1 _2 (<= 0 _2) _!))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.2 _1 _2 true _!))))
; %main bb3
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 (not false) _!))
  (%main.3 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 true (<= _2 1000000) _!))
  (%main.3 _1 _2 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_10 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 (not false) _!))
  (%main.7 _1 _2 _10 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_10 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 (not true) _!))
  (%main.7 _1 _2 _10 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.11 _1 _2 _1 _2 (> _2 0) _!))
  (%main.8 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 true _!))))
; %main bb11
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.12 _1 _2 _3 _4 (not (= _3 (+ _1 _2))) _!))
  (%main.11 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.11 _1 _2 (+ _3 1) (- _4 1) (> (- _4 1) 0) _!))
  (%main.11 _1 _2 _3 _4 true _!))))
; %main bb12
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.12 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.12 _1 _2 _3 _4 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
