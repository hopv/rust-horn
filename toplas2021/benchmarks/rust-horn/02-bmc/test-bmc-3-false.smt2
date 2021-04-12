(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Bool Bool) Bool)
(declare-fun %main.5 (Int Bool Bool) Bool)
(declare-fun %main.9 (Int Bool Bool) Bool)
(declare-fun %main.13 (Int Bool Bool) Bool)
(declare-fun %main.17 (Int Bool Bool) Bool)
(declare-fun %main.21 (Int Bool Bool) Bool)
(declare-fun %main.24 (Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 0 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 (+ _1 2) _?.4 _!))
  (%main.1 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 (+ _1 1) _?.4 _!))
  (%main.1 _1 true _!))))
; %main bb5
(assert (forall ((_1 Int) (_! Bool) (_?.8 Bool)) (=>
  (and (%main.9 (+ _1 2) _?.8 _!))
  (%main.5 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool) (_?.8 Bool)) (=>
  (and (%main.9 (+ _1 1) _?.8 _!))
  (%main.5 _1 true _!))))
; %main bb9
(assert (forall ((_1 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 (+ _1 2) _?.12 _!))
  (%main.9 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 (+ _1 1) _?.12 _!))
  (%main.9 _1 true _!))))
; %main bb13
(assert (forall ((_1 Int) (_! Bool) (_?.16 Bool)) (=>
  (and (%main.17 (+ _1 2) _?.16 _!))
  (%main.13 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool) (_?.16 Bool)) (=>
  (and (%main.17 (+ _1 1) _?.16 _!))
  (%main.13 _1 true _!))))
; %main bb17
(assert (forall ((_1 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.21 (+ _1 2) _?.20 _!))
  (%main.17 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.21 (+ _1 1) _?.20 _!))
  (%main.17 _1 true _!))))
; %main bb21
(assert (forall ((_1 Int) (_! Bool)) (=>
  (and (%main.24 (+ _1 3) (not (<= (+ _1 3) 12)) _!))
  (%main.21 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool)) (=>
  (and (%main.24 (+ _1 1) (not (<= (+ _1 1) 12)) _!))
  (%main.21 _1 true _!))))
; %main bb24
(assert (forall ((_1 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.24 _1 false _!))))
(assert (forall ((_1 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.24 _1 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
