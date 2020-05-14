(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %linger_dec (~Mut<Int>) Bool)
(declare-fun %linger_dec.1 (~Mut<Int> Bool) Bool)
(declare-fun %linger_dec.6 (~Mut<Int> Int Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Bool Bool) Bool)

; %linger_dec
(assert (forall ((_1 ~Mut<Int>) (_?.0 Bool)) (=>
  (and (%linger_dec.1 (~mut<Int> (- (~cur<Int> _1) 1) (~ret<Int> _1)) _?.0))
  (%linger_dec _1))))
; %linger_dec bb1
(assert (forall ((_1 ~Mut<Int>) (_?.2 Int) (_?.5 Bool)) (=>
  (and (%linger_dec.6 _1 _?.2 _?.5))
  (%linger_dec.1 _1 false))))
(assert (forall ((_1 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec.1 _1 true))))
; %linger_dec bb6
(assert (forall ((_1 ~Mut<Int>) (_3 Int) (_*.7_1 Int) (_*.7_2 Int) (_*.9_0 Int)) (=>
  (and (= _*.7_1 _*.7_2) (%linger_dec (~mut<Int> (~cur<Int> _1) _*.9_0)) (= _*.7_2 _*.9_0) (= (~ret<Int> _1) _*.7_1) true)
  (%linger_dec.6 _1 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_3 Int) (_*.8_2 Int) (_*.8_3 Int) (_*.8_4 Int) (_*.9_0 Int)) (=>
  (and (= _*.8_2 _*.8_3) (= _*.8_3 _*.8_4) (%linger_dec (~mut<Int> _3 _*.9_0)) (= _*.8_4 _*.9_0) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec.6 _1 _3 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_*.1_5 Int) (_*.1_6 Int)) (=>
  (and (%linger_dec (~mut<Int> _?.0 _*.1_6)) (= _*.1_5 _*.1_6) (%main.2 (not (> (- _?.0 1) _*.1_5)) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.2 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
