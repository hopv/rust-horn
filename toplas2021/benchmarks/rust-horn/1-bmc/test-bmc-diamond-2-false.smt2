(set-logic HORN)

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.5 (Int Int Bool Bool) Bool)
(declare-fun %main.8 (Int Int Bool Bool) Bool)
(declare-fun %main.12 (Int Int Bool Bool) Bool)
(declare-fun %main.15 (Int Int Bool Bool) Bool)
(declare-fun %main.19 (Int Int Bool Bool) Bool)
(declare-fun %main.22 (Int Int Bool Bool) Bool)
(declare-fun %main.26 (Int Int Bool Bool) Bool)
(declare-fun %main.29 (Int Int Bool Bool) Bool)
(declare-fun %main.33 (Int Int Bool Bool) Bool)
(declare-fun %main.36 (Int Int Bool Bool) Bool)
(declare-fun %main.40 (Int Int Bool Bool) Bool)
(declare-fun %main.43 (Int Int Bool Bool) Bool)
(declare-fun %main.45 (Bool Bool) Bool)

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
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.6 Bool)) (=>
  (and (%main.8 _1 _2 _?.6 _!))
  (%main.5 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.4 Bool)) (=>
  (and (%main.5 _1 _2 _?.4 _!))
  (%main.5 _1 _2 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.11 Bool)) (=>
  (and (%main.12 _1 _2 _?.11 _!))
  (%main.8 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.11 Bool)) (=>
  (and (%main.12 (+ _1 1) (+ _2 1) _?.11 _!))
  (%main.8 _1 _2 true _!))))
; %main bb12
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.13 Bool)) (=>
  (and (%main.15 _1 _2 _?.13 _!))
  (%main.12 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.11 Bool)) (=>
  (and (%main.12 _1 _2 _?.11 _!))
  (%main.12 _1 _2 true _!))))
; %main bb15
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _?.18 _!))
  (%main.15 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 (+ _1 1) (+ _2 1) _?.18 _!))
  (%main.15 _1 _2 true _!))))
; %main bb19
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.22 _1 _2 _?.20 _!))
  (%main.19 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _?.18 _!))
  (%main.19 _1 _2 true _!))))
; %main bb22
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.25 Bool)) (=>
  (and (%main.26 _1 _2 _?.25 _!))
  (%main.22 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.25 Bool)) (=>
  (and (%main.26 (+ _1 1) (+ _2 1) _?.25 _!))
  (%main.22 _1 _2 true _!))))
; %main bb26
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.27 Bool)) (=>
  (and (%main.29 _1 _2 _?.27 _!))
  (%main.26 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.25 Bool)) (=>
  (and (%main.26 _1 _2 _?.25 _!))
  (%main.26 _1 _2 true _!))))
; %main bb29
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.32 Bool)) (=>
  (and (%main.33 _1 _2 _?.32 _!))
  (%main.29 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.32 Bool)) (=>
  (and (%main.33 (+ _1 1) (+ _2 1) _?.32 _!))
  (%main.29 _1 _2 true _!))))
; %main bb33
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.34 Bool)) (=>
  (and (%main.36 _1 _2 _?.34 _!))
  (%main.33 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.32 Bool)) (=>
  (and (%main.33 _1 _2 _?.32 _!))
  (%main.33 _1 _2 true _!))))
; %main bb36
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.39 Bool)) (=>
  (and (%main.40 _1 _2 _?.39 _!))
  (%main.36 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.39 Bool)) (=>
  (and (%main.40 (+ _1 1) (+ _2 1) _?.39 _!))
  (%main.36 _1 _2 true _!))))
; %main bb40
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.41 Bool)) (=>
  (and (%main.43 _1 _2 _?.41 _!))
  (%main.40 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_?.39 Bool)) (=>
  (and (%main.40 _1 _2 _?.39 _!))
  (%main.40 _1 _2 true _!))))
; %main bb43
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.45 (not (> _1 _2)) _!))
  (%main.43 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (%main.45 (not (> (+ _1 1) (+ _2 1))) _!))
  (%main.43 _1 _2 true _!))))
; %main bb45
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.45 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.45 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
