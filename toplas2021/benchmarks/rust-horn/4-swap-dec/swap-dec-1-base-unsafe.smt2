(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.3 (Int Int Int Bool Bool) Bool)
(declare-fun %main.6 (Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %swap_dec (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %swap_dec.2 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_*.2_6 Int) (_*.2_7 ~Mut<Int>) (_*.2_8 ~Mut<Int>) (_*.2_12 Int) (_*.2_13 ~Mut<Int>) (_*.2_14 ~Mut<Int>)) (=>
  (and (%swap_dec (~mut<~Mut<Int>> (~mut<Int> _?.0 _*.2_6) _*.2_8) (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.2_12) _*.2_14)) (= (~ret<Int> _*.2_13) (~cur<Int> _*.2_13)) (= _*.2_13 _*.2_14) (= (~ret<Int> _*.2_7) (~cur<Int> _*.2_7)) (= _*.2_7 _*.2_8) (%main.3 _*.2_6 _*.2_12 _?.0 (>= _?.0 _*.2_6) _!))
  (%main _!))))
; %main bb3
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.3 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.6 _1 _2 _3 true (<= (- _3 _1) 3) _!))
  (%main.3 _1 _2 _3 true _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_13 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.6 _1 _2 _3 _13 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_13 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not true) _!))
  (%main.6 _1 _2 _3 _13 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.7 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.7 _1 _2 _3 true _!))))

; %may_swap<~Mut<Int>>
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<Int>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<Int>> _1 _2))))
; %may_swap<~Mut<Int>> bb1
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.3_2 ~Mut<Int>) (_*.3_4 ~Mut<Int>)) (=>
  (and (= _*.3_4 (~cur<~Mut<Int>> _1)) (= _*.3_2 (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _2) _*.3_4) (= (~ret<~Mut<Int>> _1) _*.3_2) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 true))))

; %swap_dec
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_?.1 Bool) (_*.0_2 ~Mut<Int>) (_*.0_4 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _1) _*.0_2) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _2) _*.0_4)) (%swap_dec.2 (~mut<~Mut<Int>> _*.0_2 (~ret<~Mut<Int>> _1)) (~mut<~Mut<Int>> _*.0_4 (~ret<~Mut<Int>> _2)) _?.1))
  (%swap_dec _1 _2))))
; %swap_dec bb2
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.3_5 ~Mut<Int>) (_*.3_7 ~Mut<Int>)) (=>
  (and (%swap_dec (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _1)) 1) (~ret<Int> (~cur<~Mut<Int>> _1))) _*.3_5) (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _2)) 2) (~ret<Int> (~cur<~Mut<Int>> _2))) _*.3_7)) (= (~ret<~Mut<Int>> _1) _*.3_5) (= (~ret<~Mut<Int>> _2) _*.3_7) true)
  (%swap_dec.2 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) true)
  (%swap_dec.2 _1 _2 true))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
