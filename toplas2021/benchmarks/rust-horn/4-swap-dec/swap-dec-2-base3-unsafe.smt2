(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %swap_dec_three (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %swap_dec_three.4 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_6 Int) (_*.3_7 ~Mut<Int>) (_*.3_8 ~Mut<Int>) (_*.3_12 Int) (_*.3_13 ~Mut<Int>) (_*.3_14 ~Mut<Int>) (_*.3_18 Int) (_*.3_19 ~Mut<Int>) (_*.3_20 ~Mut<Int>)) (=>
  (and (%swap_dec_three (~mut<~Mut<Int>> (~mut<Int> _?.0 _*.3_6) _*.3_8) (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.3_12) _*.3_14) (~mut<~Mut<Int>> (~mut<Int> _?.2 _*.3_18) _*.3_20)) (= (~ret<Int> _*.3_19) (~cur<Int> _*.3_19)) (= _*.3_19 _*.3_20) (= (~ret<Int> _*.3_13) (~cur<Int> _*.3_13)) (= _*.3_13 _*.3_14) (= (~ret<Int> _*.3_7) (~cur<Int> _*.3_7)) (= _*.3_7 _*.3_8) (%main.4 _*.3_6 _*.3_12 _*.3_18 _?.0 (>= _?.0 _*.3_6) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not false) _!))
  (%main.4 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 _4 true (<= (- _4 _1) 3) _!))
  (%main.4 _1 _2 _3 _4 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_17 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not false) _!))
  (%main.7 _1 _2 _3 _4 _17 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_17 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not true) _!))
  (%main.7 _1 _2 _3 _4 _17 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.8 _1 _2 _3 _4 true _!))))

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

; %swap_dec_three
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>) (_?.3 Bool) (_*.0_2 ~Mut<Int>) (_*.0_4 ~Mut<Int>) (_*.1_5 ~Mut<Int>) (_*.1_7 ~Mut<Int>) (_*.2_5 ~Mut<Int>) (_*.2_7 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _1) _*.0_2) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _2) _*.0_4)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.0_4 _*.1_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _3) _*.1_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.0_2 _*.2_5) (~mut<~Mut<Int>> _*.1_5 _*.2_7)) (%swap_dec_three.4 (~mut<~Mut<Int>> _*.2_5 (~ret<~Mut<Int>> _1)) (~mut<~Mut<Int>> _*.2_7 (~ret<~Mut<Int>> _2)) (~mut<~Mut<Int>> _*.1_7 (~ret<~Mut<Int>> _3)) _?.3))
  (%swap_dec_three _1 _2 _3))))
; %swap_dec_three bb4
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>) (_*.5_6 ~Mut<Int>) (_*.5_8 ~Mut<Int>) (_*.5_10 ~Mut<Int>)) (=>
  (and (%swap_dec_three (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _1)) 1) (~ret<Int> (~cur<~Mut<Int>> _1))) _*.5_6) (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _2)) 2) (~ret<Int> (~cur<~Mut<Int>> _2))) _*.5_8) (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _3)) 3) (~ret<Int> (~cur<~Mut<Int>> _3))) _*.5_10)) (= (~ret<~Mut<Int>> _1) _*.5_6) (= (~ret<~Mut<Int>> _3) _*.5_10) (= (~ret<~Mut<Int>> _2) _*.5_8) true)
  (%swap_dec_three.4 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) (= (~ret<~Mut<Int>> _3) (~cur<~Mut<Int>> _3)) (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) true)
  (%swap_dec_three.4 _1 _2 _3 true))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
