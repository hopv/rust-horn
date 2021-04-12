(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.6 (Int Int Bool Bool) Bool)
(declare-fun %main.9 (Int Int Bool Bool) Bool)
(declare-fun %main.14 (Int Int Bool Bool) Bool)
(declare-fun %main.17 (Int Int Bool Bool) Bool)
(declare-fun %main.22 (Int Int Bool Bool) Bool)
(declare-fun %main.25 (Int Int Bool Bool) Bool)
(declare-fun %main.30 (Int Int Bool Bool) Bool)
(declare-fun %main.33 (Int Int Bool Bool) Bool)
(declare-fun %main.38 (Int Int Bool Bool) Bool)
(declare-fun %main.41 (Int Int Bool Bool) Bool)
(declare-fun %main.46 (Int Int Bool Bool) Bool)
(declare-fun %main.49 (Int Int Bool Bool) Bool)
(declare-fun %main.52 (Int Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 1 1 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.5 Bool)) (=>
  (and (%main.6 _1 _2 _?.5 _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.5 Bool)) (=>
  (and (%main.6 (+ _1 1) (+ _2 1) _?.5 _!))
  (%main.1 _1 _2 true _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.7 Bool)) (=>
  (and (%main.9 _1 _2 _?.7 _!))
  (%main.6 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.5 Bool)) (=>
  (and (%main.6 _1 _2 _?.5 _!))
  (%main.6 _1 _2 true _!))))
; %main bb9
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.13 Bool)) (=>
  (and (%main.14 _1 _2 _?.13 _!))
  (%main.9 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.13 Bool)) (=>
  (and (%main.14 (+ _1 1) (+ _2 1) _?.13 _!))
  (%main.9 _1 _2 true _!))))
; %main bb14
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.15 Bool)) (=>
  (and (%main.17 _1 _2 _?.15 _!))
  (%main.14 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.13 Bool)) (=>
  (and (%main.14 _1 _2 _?.13 _!))
  (%main.14 _1 _2 true _!))))
; %main bb17
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.21 Bool)) (=>
  (and (%main.22 _1 _2 _?.21 _!))
  (%main.17 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.21 Bool)) (=>
  (and (%main.22 (+ _1 1) (+ _2 1) _?.21 _!))
  (%main.17 _1 _2 true _!))))
; %main bb22
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.23 Bool)) (=>
  (and (%main.25 _1 _2 _?.23 _!))
  (%main.22 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.21 Bool)) (=>
  (and (%main.22 _1 _2 _?.21 _!))
  (%main.22 _1 _2 true _!))))
; %main bb25
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.29 Bool)) (=>
  (and (%main.30 _1 _2 _?.29 _!))
  (%main.25 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.29 Bool)) (=>
  (and (%main.30 (+ _1 1) (+ _2 1) _?.29 _!))
  (%main.25 _1 _2 true _!))))
; %main bb30
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.31 Bool)) (=>
  (and (%main.33 _1 _2 _?.31 _!))
  (%main.30 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.29 Bool)) (=>
  (and (%main.30 _1 _2 _?.29 _!))
  (%main.30 _1 _2 true _!))))
; %main bb33
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.37 Bool)) (=>
  (and (%main.38 _1 _2 _?.37 _!))
  (%main.33 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.37 Bool)) (=>
  (and (%main.38 (+ _1 1) (+ _2 1) _?.37 _!))
  (%main.33 _1 _2 true _!))))
; %main bb38
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.39 Bool)) (=>
  (and (%main.41 _1 _2 _?.39 _!))
  (%main.38 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.37 Bool)) (=>
  (and (%main.38 _1 _2 _?.37 _!))
  (%main.38 _1 _2 true _!))))
; %main bb41
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.45 Bool)) (=>
  (and (%main.46 _1 _2 _?.45 _!))
  (%main.41 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.45 Bool)) (=>
  (and (%main.46 (+ _1 1) (+ _2 1) _?.45 _!))
  (%main.41 _1 _2 true _!))))
; %main bb46
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.47 Bool)) (=>
  (and (%main.49 _1 _2 _?.47 _!))
  (%main.46 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.45 Bool)) (=>
  (and (%main.46 _1 _2 _?.45 _!))
  (%main.46 _1 _2 true _!))))
; %main bb49
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.52 _1 _2 (not (> _1 _2)) _!))
  (%main.49 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.52 (+ _1 1) (+ _2 1) (not (> (+ _1 1) (+ _2 1))) _!))
  (%main.49 _1 _2 true _!))))
; %main bb52
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.52 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.52 _1 _2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
