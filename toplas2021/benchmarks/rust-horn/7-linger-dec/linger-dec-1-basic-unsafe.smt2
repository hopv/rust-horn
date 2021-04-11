(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %linger_dec (~Mut<Int>) Bool)
(declare-fun %linger_dec.1 (~Mut<Int> Bool) Bool)
(declare-fun %linger_dec.5 (~Mut<Int> Int Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)

; %linger_dec
(assert (forall ((_1 ~Mut<Int>) (_?.0 Bool)) (=>
  (and (%linger_dec.1 (~mut<Int> (- (~cur<Int> _1) 1) (~ret<Int> _1)) _?.0))
  (%linger_dec _1))))
; %linger_dec bb1
(assert (forall ((_1 ~Mut<Int>) (_?.3 Int) (_?.4 Bool)) (=>
  (and (%linger_dec.5 _1 _?.3 _?.4))
  (%linger_dec.1 _1 false))))
(assert (forall ((_1 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec.1 _1 true))))
; %linger_dec bb5
(assert (forall ((_1 ~Mut<Int>) (_3 Int) (_*.7_1 Int) (_*.7_2 Int) (_*.8_0 Int)) (=>
  (and (= _*.7_1 _*.7_2) (%linger_dec (~mut<Int> (~cur<Int> _1) _*.8_0)) (= _*.7_2 _*.8_0) (= (~ret<Int> _1) _*.7_1) true)
  (%linger_dec.5 _1 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_3 Int) (_*.6_2 Int) (_*.6_3 Int) (_*.6_4 Int) (_*.8_0 Int)) (=>
  (and (= _*.6_2 _*.6_3) (= _*.6_3 _*.6_4) (%linger_dec (~mut<Int> _3 _*.8_0)) (= _*.6_4 _*.8_0) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec.5 _1 _3 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_*.1_5 Int) (_*.1_6 Int)) (=>
  (and (%linger_dec (~mut<Int> _?.0 _*.1_6)) (= _*.1_5 _*.1_6) (%main.2 _*.1_5 _?.0 (not (> (- _?.0 1) _*.1_5)) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.2 _1 _2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
