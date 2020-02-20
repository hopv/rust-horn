(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)
(declare-fun %main.3 (Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.1 Bool)) (=>
  (and (%main.2 1 1 _?.1 _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.3 (not (>= _2 1)) _!))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.1 Bool)) (=>
  (and (%main.2 (+ _1 _2) (+ _1 _2) _?.1 _!))
  (%main.2 _1 _2 true _!))))
; %main bb3
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.3 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
