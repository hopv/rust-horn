(set-logic HORN)

(declare-fun %assume (Bool) Bool)
(declare-fun %assume.0 (Bool Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.6 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.11 (Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.14 (Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.19 (Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.22 (Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.27 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.28 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.34 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.35 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.41 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.42 (Int Int Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.46 (Int Int Int Int Int Int Int Bool Bool) Bool)

; %assume
(assert (forall ((_1 Bool)) (=>
  (and (%assume.0 _1 (not _1)))
  (%assume _1))))
; %assume bb0
(assert (forall ((_1 Bool)) (=>
  (and true)
  (%assume.0 _1 false))))
(assert (forall ((_1 Bool)) (=>
  (and false)
  (%assume.0 _1 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.2 Int) (_?.3 Int) (_?.4 Int) (_?.5 Bool)) (=>
  (and (%assume (>= _?.0 0)) (%main.6 _?.2 _?.3 _?.4 _?.0 _?.5 _!))
  (%main _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_7 Int) (_! Bool) (_?.10 Bool)) (=>
  (and (%main.11 _1 _2 _3 0 _7 _?.10 _!))
  (%main.6 _1 _2 _3 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_7 Int) (_! Bool) (_?.10 Bool)) (=>
  (and (%main.11 _1 _2 _3 1 _7 _?.10 _!))
  (%main.6 _1 _2 _3 _7 true _!))))
; %main bb11
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_7 Int) (_! Bool) (_?.12 Bool)) (=>
  (and (%main.14 _1 _2 _3 _4 _7 _?.12 _!))
  (%main.11 _1 _2 _3 _4 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_7 Int) (_! Bool) (_?.10 Bool)) (=>
  (and (%main.11 _1 _2 _3 _4 _7 _?.10 _!))
  (%main.11 _1 _2 _3 _4 _7 true _!))))
; %main bb14
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_7 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _3 _4 0 _7 _?.18 _!))
  (%main.14 _1 _2 _3 _4 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_7 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _3 _4 1 _7 _?.18 _!))
  (%main.14 _1 _2 _3 _4 _7 true _!))))
; %main bb19
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_7 Int) (_! Bool) (_?.20 Bool)) (=>
  (and (%main.22 _1 _2 _3 _4 _5 _7 _?.20 _!))
  (%main.19 _1 _2 _3 _4 _5 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_7 Int) (_! Bool) (_?.18 Bool)) (=>
  (and (%main.19 _1 _2 _3 _4 _5 _7 _?.18 _!))
  (%main.19 _1 _2 _3 _4 _5 _7 true _!))))
; %main bb22
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_7 Int) (_! Bool) (_?.26 Bool)) (=>
  (and (%main.27 _1 _2 _3 _4 _5 0 _7 _?.26 _!))
  (%main.22 _1 _2 _3 _4 _5 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_7 Int) (_! Bool) (_?.26 Bool)) (=>
  (and (%main.27 _1 _2 _3 _4 _5 1 _7 _?.26 _!))
  (%main.22 _1 _2 _3 _4 _5 _7 true _!))))
; %main bb27
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (%main.28 _1 _2 _3 _4 _5 _6 _7 (not (= _4 0)) _!))
  (%main.27 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.26 Bool)) (=>
  (and (%main.27 _1 _2 _3 _4 _5 _6 _7 _?.26 _!))
  (%main.27 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb28
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.33 Bool)) (=>
  (and (%main.34 (- _1 1) _2 _3 _4 _5 _6 _7 _?.33 _!))
  (%main.28 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.33 Bool)) (=>
  (and (%main.34 (+ _1 1) _2 _3 _4 _5 _6 _7 _?.33 _!))
  (%main.28 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb34
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (%main.35 _1 _2 _3 _4 _5 _6 _7 (not (= _5 0)) _!))
  (%main.34 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.33 Bool)) (=>
  (and (%main.34 _1 _2 _3 _4 _5 _6 _7 _?.33 _!))
  (%main.34 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb35
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.40 Bool)) (=>
  (and (%main.41 _1 (- _2 1) _3 _4 _5 _6 _7 _?.40 _!))
  (%main.35 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.40 Bool)) (=>
  (and (%main.41 _1 (+ _2 1) _3 _4 _5 _6 _7 _?.40 _!))
  (%main.35 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb41
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (%main.42 _1 _2 _3 _4 _5 _6 _7 (not (= _6 0)) _!))
  (%main.41 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool) (_?.40 Bool)) (=>
  (and (%main.41 _1 _2 _3 _4 _5 _6 _7 _?.40 _!))
  (%main.41 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb42
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (%main.46 _1 _2 (- _3 1) _4 _5 _6 _7 (not (> _7 0)) _!))
  (%main.42 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (%main.46 _1 _2 (+ _3 1) _4 _5 _6 _7 (not (> _7 0)) _!))
  (%main.42 _1 _2 _3 _4 _5 _6 _7 true _!))))
; %main bb46
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.46 _1 _2 _3 _4 _5 _6 _7 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_6 Int) (_7 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.46 _1 _2 _3 _4 _5 _6 _7 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
