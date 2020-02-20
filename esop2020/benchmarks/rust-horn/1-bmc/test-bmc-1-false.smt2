(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.4 (Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Bool Bool) Bool)
(declare-fun %main.10 (Int Int Bool Bool) Bool)
(declare-fun %main.13 (Int Int Bool Bool) Bool)
(declare-fun %main.16 (Int Int Bool Bool) Bool)
(declare-fun %main.19 (Int Int Bool Bool) Bool)
(declare-fun %main.22 (Int Int Bool Bool) Bool)
(declare-fun %main.25 (Int Int Bool Bool) Bool)
(declare-fun %main.28 (Int Int Bool Bool) Bool)
(declare-fun %main.30 (Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 1 1 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.3 Bool)) (=>
  (and (%main.4 _1 _2 _?.3 _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.3 Bool)) (=>
  (and (%main.4 (+ _1 1) (+ _2 1) _?.3 _!))
  (%main.1 _1 _2 true _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.6 Bool)) (=>
  (and (%main.7 _1 _2 _?.6 _!))
  (%main.4 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.6 Bool)) (=>
  (and (%main.7 (+ _1 1) (+ _2 1) _?.6 _!))
  (%main.4 _1 _2 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.9 Bool)) (=>
  (and (%main.10 _1 _2 _?.9 _!))
  (%main.7 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.9 Bool)) (=>
  (and (%main.10 (+ _1 1) (+ _2 1) _?.9 _!))
  (%main.7 _1 _2 true _!))))
; %main bb10
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 _1 _2 _?.12 _!))
  (%main.10 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.13 (+ _1 1) (+ _2 1) _?.12 _!))
  (%main.10 _1 _2 true _!))))
; %main bb13
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.15 Bool)) (=>
  (and (%main.16 _1 _2 _?.15 _!))
  (%main.13 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.15 Bool)) (=>
  (and (%main.16 (+ _1 1) (+ _2 1) _?.15 _!))
  (%main.13 _1 _2 true _!))))
; %main bb16
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _?.18 _!))
  (%main.16 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 (+ _1 1) (+ _2 1) _?.18 _!))
  (%main.16 _1 _2 true _!))))
; %main bb19
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.21 Bool)) (=>
  (and (%main.22 _1 _2 _?.21 _!))
  (%main.19 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.21 Bool)) (=>
  (and (%main.22 (+ _1 1) (+ _2 1) _?.21 _!))
  (%main.19 _1 _2 true _!))))
; %main bb22
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.24 Bool)) (=>
  (and (%main.25 _1 _2 _?.24 _!))
  (%main.22 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.24 Bool)) (=>
  (and (%main.25 (+ _1 1) (+ _2 1) _?.24 _!))
  (%main.22 _1 _2 true _!))))
; %main bb25
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.27 Bool)) (=>
  (and (%main.28 _1 _2 _?.27 _!))
  (%main.25 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.27 Bool)) (=>
  (and (%main.28 (+ _1 1) (+ _2 1) _?.27 _!))
  (%main.25 _1 _2 true _!))))
; %main bb28
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.30 (not (<= _1 10)) _!))
  (%main.28 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.30 (not (<= (+ _1 1) 10)) _!))
  (%main.28 _1 _2 true _!))))
; %main bb30
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.30 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.30 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
