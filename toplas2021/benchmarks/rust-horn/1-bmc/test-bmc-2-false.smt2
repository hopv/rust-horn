(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)
(declare-fun %main.3 (Bool Bool) Bool)
(declare-fun %main.5 (Int Int Bool Bool Bool) Bool)
(declare-fun %main.8 (Int Int Bool Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.1 Bool)) (=>
  (and (%main.2 1 1 _?.1 _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.3 (not (= _1 _2)) _!))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 _1 _2 true _?.4 _!))
  (%main.2 _1 _2 true _!))))
; %main bb3
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.3 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.3 true _!))))
; %main bb5
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool) (_?.7 Bool)) (=>
  (and (%main.8 _1 _2 _3 _?.7 _!))
  (%main.5 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool) (_?.7 Bool)) (=>
  (and (%main.8 (+ _1 1) (+ _2 1) _3 _?.7 _!))
  (%main.5 _1 _2 _3 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool) (_?.1 Bool)) (=>
  (and (%main.2 _1 _2 _?.1 _!))
  (%main.8 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Bool) (_! Bool) (_?.1 Bool)) (=>
  (and (%main.2 (+ _1 1) _2 _?.1 _!))
  (%main.8 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
