(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.5 (Int Int Bool Bool) Bool)
(declare-fun %main.9 (Int Int Bool Bool) Bool)
(declare-fun %main.13 (Int Int Bool Bool) Bool)
(declare-fun %main.17 (Int Int Bool Bool) Bool)
(declare-fun %main.21 (Int Int Bool Bool) Bool)
(declare-fun %main.25 (Int Int Bool Bool) Bool)
(declare-fun %main.29 (Int Int Bool Bool) Bool)
(declare-fun %main.33 (Int Int Bool Bool) Bool)
(declare-fun %main.37 (Int Int Bool Bool) Bool)
(declare-fun %main.40 (Int Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 1 1 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 _1 _2 _?.4 _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 (+ _1 1) (+ _2 1) _?.4 _!))
  (%main.1 _1 _2 true _!))))
; %main bb5
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.8 Bool)) (=>
  (and (%main.9 _1 _2 _?.8 _!))
  (%main.5 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.8 Bool)) (=>
  (and (%main.9 (+ _1 1) (+ _2 1) _?.8 _!))
  (%main.5 _1 _2 true _!))))
; %main bb9
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 _1 _2 _?.12 _!))
  (%main.9 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 (+ _1 1) (+ _2 1) _?.12 _!))
  (%main.9 _1 _2 true _!))))
; %main bb13
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.16 Bool)) (=>
  (and (%main.17 _1 _2 _?.16 _!))
  (%main.13 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.16 Bool)) (=>
  (and (%main.17 (+ _1 1) (+ _2 1) _?.16 _!))
  (%main.13 _1 _2 true _!))))
; %main bb17
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.21 _1 _2 _?.20 _!))
  (%main.17 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.21 (+ _1 1) (+ _2 1) _?.20 _!))
  (%main.17 _1 _2 true _!))))
; %main bb21
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.24 Bool)) (=>
  (and (%main.25 _1 _2 _?.24 _!))
  (%main.21 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.24 Bool)) (=>
  (and (%main.25 (+ _1 1) (+ _2 1) _?.24 _!))
  (%main.21 _1 _2 true _!))))
; %main bb25
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.28 Bool)) (=>
  (and (%main.29 _1 _2 _?.28 _!))
  (%main.25 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.28 Bool)) (=>
  (and (%main.29 (+ _1 1) (+ _2 1) _?.28 _!))
  (%main.25 _1 _2 true _!))))
; %main bb29
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.32 Bool)) (=>
  (and (%main.33 _1 _2 _?.32 _!))
  (%main.29 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.32 Bool)) (=>
  (and (%main.33 (+ _1 1) (+ _2 1) _?.32 _!))
  (%main.29 _1 _2 true _!))))
; %main bb33
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.36 Bool)) (=>
  (and (%main.37 _1 _2 _?.36 _!))
  (%main.33 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.36 Bool)) (=>
  (and (%main.37 (+ _1 1) (+ _2 1) _?.36 _!))
  (%main.33 _1 _2 true _!))))
; %main bb37
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.40 _1 _2 (not (<= _1 10)) _!))
  (%main.37 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.40 (+ _1 1) (+ _2 1) (not (<= (+ _1 1) 10)) _!))
  (%main.37 _1 _2 true _!))))
; %main bb40
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.40 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.40 _1 _2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
