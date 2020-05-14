(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %linger_dec_bound (Int ~Mut<Int>) Bool)
(declare-fun %linger_dec_bound.0 (Int ~Mut<Int> Bool) Bool)
(declare-fun %linger_dec_bound.4 (Int ~Mut<Int> Int Int Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.3 (Int Int Int Bool Bool) Bool)
(declare-fun %main.6 (Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Bool Bool) Bool)

; %linger_dec_bound
(assert (forall ((_1 Int) (_2 ~Mut<Int>)) (=>
  (and (%linger_dec_bound.0 _1 _2 (= _1 0)))
  (%linger_dec_bound _1 _2))))
; %linger_dec_bound bb0
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_?.1 Int) (_?.3 Bool)) (=>
  (and (%linger_dec_bound.4 _1 (~mut<Int> (- (~cur<Int> _2) 1) (~ret<Int> _2)) _?.1 (- _1 1) _?.3))
  (%linger_dec_bound.0 _1 _2 false))))
(assert (forall ((_1 Int) (_2 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _2) (~cur<Int> _2)) true)
  (%linger_dec_bound.0 _1 _2 true))))
; %linger_dec_bound bb4
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_5 Int) (_7 Int) (_*.5_1 Int) (_*.5_2 Int) (_*.7_0 Int)) (=>
  (and (= _*.5_1 _*.5_2) (%linger_dec_bound _7 (~mut<Int> (~cur<Int> _2) _*.7_0)) (= _*.5_2 _*.7_0) (= (~ret<Int> _2) _*.5_1) true)
  (%linger_dec_bound.4 _1 _2 _5 _7 false))))
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_5 Int) (_7 Int) (_*.6_2 Int) (_*.6_3 Int) (_*.6_4 Int) (_*.7_0 Int)) (=>
  (and (= _*.6_2 _*.6_3) (= _*.6_3 _*.6_4) (%linger_dec_bound _7 (~mut<Int> _5 _*.7_0)) (= _*.6_4 _*.7_0) (= (~ret<Int> _2) (~cur<Int> _2)) true)
  (%linger_dec_bound.4 _1 _2 _5 _7 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_*.2_7 Int) (_*.2_8 Int)) (=>
  (and (%linger_dec_bound _?.0 (~mut<Int> _?.1 _*.2_8)) (= _*.2_7 _*.2_8) (%main.3 _?.0 _*.2_7 _?.1 (>= _?.1 _*.2_7) _!))
  (%main _!))))
; %main bb3
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.3 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.6 _1 _2 _3 true (<= (- _3 _2) _1) _!))
  (%main.3 _1 _2 _3 true _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_10 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.6 _1 _2 _3 _10 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_10 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not true) _!))
  (%main.6 _1 _2 _3 _10 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.7 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.7 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
