(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %linger_dec_three (~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %linger_dec_three.1 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %linger_dec_three.6 (~Mut<Int> ~Mut<Int> ~Mut<Int> Int ~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %linger_dec_three.9 (~Mut<Int> ~Mut<Int> ~Mut<Int> Int ~Mut<Int> ~Mut<Int> ~Mut<Int> Bool Bool) Bool)
(declare-fun %linger_dec_three.12 (~Mut<Int> ~Mut<Int> ~Mut<Int> Int ~Mut<Int> ~Mut<Int> ~Mut<Int> Bool Bool Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Bool Bool) Bool)

; %linger_dec_three
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_?.0 Bool)) (=>
  (and (%linger_dec_three.1 (~mut<Int> (- (~cur<Int> _1) 1) (~ret<Int> _1)) (~mut<Int> (- (~cur<Int> _2) 2) (~ret<Int> _2)) (~mut<Int> (- (~cur<Int> _3) 3) (~ret<Int> _3)) _?.0))
  (%linger_dec_three _1 _2 _3))))
; %linger_dec_three bb1
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_?.2 Int) (_?.5 Bool) (_%.0 ~Mut<Int>) (_%.1 ~Mut<Int>) (_%.2 ~Mut<Int>)) (=>
  (and (%linger_dec_three.6 _%.0 _%.1 _%.2 _?.2 _1 _2 _3 _?.5))
  (%linger_dec_three.1 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _1) (~cur<Int> _1)) (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _3) (~cur<Int> _3)) true)
  (%linger_dec_three.1 _1 _2 _3 true))))
; %linger_dec_three bb6
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_?.7 Bool)) (=>
  (and (%linger_dec_three.9 _1 _2 _3 _5 _6 _7 _8 false _?.7))
  (%linger_dec_three.6 _1 _2 _3 _5 _6 _7 _8 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_*.8_2 Int) (_*.8_3 Int) (_*.16_3 Int) (_*.16_5 Int) (_*.16_7 Int)) (=>
  (and (= (~ret<Int> _6) (~cur<Int> _6)) (= _*.8_2 _*.8_3) (%linger_dec_three (~mut<Int> _5 _*.16_3) (~mut<Int> (~cur<Int> _7) _*.16_5) (~mut<Int> (~cur<Int> _8) _*.16_7)) (= (~ret<Int> _8) _*.16_7) (= (~ret<Int> _7) _*.16_5) (= _*.8_3 _*.16_3) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _1) (~cur<Int> _1)) (= (~ret<Int> _2) (~cur<Int> _2)) true)
  (%linger_dec_three.6 _1 _2 _3 _5 _6 _7 _8 true))))
; %linger_dec_three bb9
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_9 Bool) (_?.10 Bool)) (=>
  (and (%linger_dec_three.12 _1 _2 _3 _5 _6 _7 _8 _9 false _?.10))
  (%linger_dec_three.9 _1 _2 _3 _5 _6 _7 _8 _9 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_9 Bool) (_*.11_2 Int) (_*.11_3 Int) (_*.16_3 Int) (_*.16_5 Int) (_*.16_7 Int)) (=>
  (and (= (~ret<Int> _7) (~cur<Int> _7)) (= _*.11_2 _*.11_3) (%linger_dec_three (~mut<Int> (~cur<Int> _6) _*.16_3) (~mut<Int> _5 _*.16_5) (~mut<Int> (~cur<Int> _8) _*.16_7)) (= (~ret<Int> _8) _*.16_7) (= _*.11_3 _*.16_5) (= (~ret<Int> _6) _*.16_3) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec_three.9 _1 _2 _3 _5 _6 _7 _8 _9 true))))
; %linger_dec_three bb12
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_9 Bool) (_12 Bool) (_*.16_3 Int) (_*.16_5 Int) (_*.16_7 Int)) (=>
  (and (%linger_dec_three (~mut<Int> (~cur<Int> _6) _*.16_3) (~mut<Int> (~cur<Int> _7) _*.16_5) (~mut<Int> (~cur<Int> _8) _*.16_7)) (= (~ret<Int> _8) _*.16_7) (= (~ret<Int> _7) _*.16_5) (= (~ret<Int> _6) _*.16_3) (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec_three.12 _1 _2 _3 _5 _6 _7 _8 _9 _12 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_5 Int) (_6 ~Mut<Int>) (_7 ~Mut<Int>) (_8 ~Mut<Int>) (_9 Bool) (_12 Bool) (_*.13_2 Int) (_*.13_3 Int) (_*.16_3 Int) (_*.16_5 Int) (_*.16_7 Int)) (=>
  (and (= (~ret<Int> _8) (~cur<Int> _8)) (= _*.13_2 _*.13_3) (%linger_dec_three (~mut<Int> (~cur<Int> _6) _*.16_3) (~mut<Int> (~cur<Int> _7) _*.16_5) (~mut<Int> _5 _*.16_7)) (= _*.13_3 _*.16_7) (= (~ret<Int> _7) _*.16_5) (= (~ret<Int> _6) _*.16_3) (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%linger_dec_three.12 _1 _2 _3 _5 _6 _7 _8 _9 _12 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_5 Int) (_*.3_6 Int) (_*.3_9 Int) (_*.3_10 Int) (_*.3_13 Int) (_*.3_14 Int)) (=>
  (and (%linger_dec_three (~mut<Int> _?.0 _*.3_6) (~mut<Int> _?.1 _*.3_10) (~mut<Int> _?.2 _*.3_14)) (= _*.3_13 _*.3_14) (= _*.3_9 _*.3_10) (= _*.3_5 _*.3_6) (%main.4 (not (> _?.0 _*.3_5)) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.4 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.4 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
