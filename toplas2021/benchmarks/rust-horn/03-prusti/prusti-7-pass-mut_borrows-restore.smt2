(set-logic HORN)

(declare-datatypes ((%T 0)) ((par () (
  (%T-0 (%T-0.0 Int))))))

(declare-datatypes ((~Mut<%T> 0)) ((par () ((~mut<%T> (~cur<%T> %T) (~ret<%T> %T))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (%T %T Bool Bool) Bool)
(declare-fun %main.4 (%T %T ~Mut<%T> Int Bool) Bool)
(declare-fun %main.7 (%T %T ~Mut<%T> Bool Bool) Bool)
(declare-fun %main.9 (%T %T ~Mut<%T> Int Bool) Bool)
(declare-fun %main.12 (%T %T ~Mut<%T> Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 (%T-0 11) (%T-0 22) _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 %T) (_2 %T) (_! Bool) (_*.3_1 %T) (_*.3_2 %T)) (=>
  (and (= _*.3_1 _*.3_2) (%main.4 (%T-0 (+ (%T-0.0 _1) 44)) (%T-0 (+ (%T-0.0 _*.3_1) 44)) (~mut<%T> (%T-0 (+ (%T-0.0 _2) 33)) _*.3_2) (+ (%T-0.0 _1) 44) _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 %T) (_2 %T) (_! Bool) (_*.2_0 %T)) (=>
  (and (%main.4 (%T-0 (+ (%T-0.0 _*.2_0) 44)) (%T-0 (+ (%T-0.0 _2) 44)) (~mut<%T> (%T-0 (+ (%T-0.0 _1) 33)) _*.2_0) (+ (%T-0.0 _*.2_0) 44) _!))
  (%main.1 _1 _2 true _!))))
; %main bb4
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not true) _!))
  (%main.4 _1 _2 _3 88 _!))))
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_8 Int) (_! Bool)) (=>
  (and (distinct _8 88) (%main.7 _1 _2 _3 (not (= (%T-0.0 _1) 55)) _!))
  (%main.4 _1 _2 _3 _8 _!))))
; %main bb7
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 (%T-0.0 _2) _!))
  (%main.7 _1 _2 _3 false _!))))
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (= (~ret<%T> _3) (~cur<%T> _3)) (= _! true))
  (%main.7 _1 _2 _3 true _!))))
; %main bb9
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (%main.12 _1 _2 _3 (not true) _!))
  (%main.9 _1 _2 _3 66 _!))))
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_13 Int) (_! Bool)) (=>
  (and (distinct _13 66) (%main.12 _1 _2 _3 (not (= (%T-0.0 _2) 99)) _!))
  (%main.9 _1 _2 _3 _13 _!))))
; %main bb12
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (= (~ret<%T> _3) (~cur<%T> _3)) (= _! false))
  (%main.12 _1 _2 _3 false _!))))
(assert (forall ((_1 %T) (_2 %T) (_3 ~Mut<%T>) (_! Bool)) (=>
  (and (= (~ret<%T> _3) (~cur<%T> _3)) (= _! true))
  (%main.12 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
