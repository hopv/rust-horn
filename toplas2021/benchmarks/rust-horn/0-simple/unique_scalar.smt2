(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.4 (Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 0 0 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_*.2_1 Int) (_*.2_2 Int)) (=>
  (and (= _*.2_1 _*.2_2) (= _*.2_2 1) (%main.4 (not (< (+ _1 1) 2)) _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_*.3_0 Int)) (=>
  (and (= _*.3_0 1) (%main.4 (not (< (+ _*.3_0 1) 2)) _!))
  (%main.1 _1 _2 true _!))))
; %main bb4
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.4 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.4 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
