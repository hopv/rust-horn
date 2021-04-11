(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))
(declare-datatypes ((~Mut<~Mut<~Mut<Int>>> 0)) ((par () ((~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>) (~ret<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (Int Int Int Int Int Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.9 (Int Int Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>> (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>>.1 (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)
(declare-fun %swap2_dec_bound_three (Int ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %swap2_dec_bound_three.6 (Int ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Int) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_?.3 Int) (_*.4_9 Int) (_*.4_10 ~Mut<Int>) (_*.4_11 ~Mut<~Mut<Int>>) (_*.4_12 ~Mut<~Mut<Int>>) (_*.4_17 Int) (_*.4_18 ~Mut<Int>) (_*.4_19 ~Mut<~Mut<Int>>) (_*.4_20 ~Mut<~Mut<Int>>) (_*.4_25 Int) (_*.4_26 ~Mut<Int>) (_*.4_27 ~Mut<~Mut<Int>>) (_*.4_28 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_bound_three _?.0 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.4_9) _*.4_10) _*.4_12) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.2 _*.4_17) _*.4_18) _*.4_20) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.3 _*.4_25) _*.4_26) _*.4_28)) (= (~ret<Int> _*.4_26) (~cur<Int> _*.4_26)) (= (~ret<~Mut<Int>> _*.4_27) (~cur<~Mut<Int>> _*.4_27)) (= _*.4_27 _*.4_28) (= (~ret<Int> _*.4_18) (~cur<Int> _*.4_18)) (= (~ret<~Mut<Int>> _*.4_19) (~cur<~Mut<Int>> _*.4_19)) (= _*.4_19 _*.4_20) (= (~ret<Int> _*.4_10) (~cur<Int> _*.4_10)) (= (~ret<~Mut<Int>> _*.4_11) (~cur<~Mut<Int>> _*.4_11)) (= _*.4_11 _*.4_12) (%main.5 _?.0 _*.4_9 _*.4_17 _*.4_25 _?.1 (>= _?.1 _*.4_9) _!))
  (%main _!))))
; %main bb5
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 _5 (not false) _!))
  (%main.5 _1 _2 _3 _4 _5 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 _5 true (<= (- _5 _2) (* 3 _1)) _!))
  (%main.5 _1 _2 _3 _4 _5 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_22 Bool) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 _5 (not false) _!))
  (%main.8 _1 _2 _3 _4 _5 _22 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_22 Bool) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 _5 (not true) _!))
  (%main.8 _1 _2 _3 _4 _5 _22 true _!))))
; %main bb9
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.9 _1 _2 _3 _4 _5 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_5 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.9 _1 _2 _3 _4 _5 true _!))))

; %may_swap<~Mut<Int>>
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<Int>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<Int>> _1 _2))))
; %may_swap<~Mut<Int>> bb1
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.2_2 ~Mut<Int>) (_*.2_4 ~Mut<Int>)) (=>
  (and (= _*.2_4 (~cur<~Mut<Int>> _1)) (= _*.2_2 (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _2) _*.2_4) (= (~ret<~Mut<Int>> _1) _*.2_2) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 true))))

; %may_swap<~Mut<~Mut<Int>>>
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<~Mut<Int>>> _1 _2))))
; %may_swap<~Mut<~Mut<Int>>> bb1
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_*.2_2 ~Mut<~Mut<Int>>) (_*.2_4 ~Mut<~Mut<Int>>)) (=>
  (and (= _*.2_4 (~cur<~Mut<~Mut<Int>>> _1)) (= _*.2_2 (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _2) _*.2_4) (= (~ret<~Mut<~Mut<Int>>> _1) _*.2_2) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 true))))

; %swap2_dec_bound_three
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_4 ~Mut<~Mut<~Mut<Int>>>) (_*.0_2 ~Mut<~Mut<Int>>) (_*.0_4 ~Mut<~Mut<Int>>) (_*.1_5 ~Mut<~Mut<Int>>) (_*.1_7 ~Mut<~Mut<Int>>) (_*.2_5 ~Mut<~Mut<Int>>) (_*.2_7 ~Mut<~Mut<Int>>) (_*.3_5 ~Mut<Int>) (_*.3_7 ~Mut<Int>) (_*.4_5 ~Mut<Int>) (_*.4_7 ~Mut<Int>) (_*.5_5 ~Mut<Int>) (_*.5_7 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _2) _*.0_2) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _3) _*.0_4)) (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> _*.0_4 _*.1_5) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _4) _*.1_7)) (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> _*.0_2 _*.2_5) (~mut<~Mut<~Mut<Int>>> _*.1_5 _*.2_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.2_5) _*.3_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.2_7) _*.3_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.3_7 _*.4_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.1_7) _*.4_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.3_5 _*.5_5) (~mut<~Mut<Int>> _*.4_5 _*.5_7)) (%swap2_dec_bound_three.6 _1 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.5_5 (~ret<~Mut<Int>> _*.2_5)) (~ret<~Mut<~Mut<Int>>> _2)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.5_7 (~ret<~Mut<Int>> _*.2_7)) (~ret<~Mut<~Mut<Int>>> _3)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.4_7 (~ret<~Mut<Int>> _*.1_7)) (~ret<~Mut<~Mut<Int>>> _4)) _1))
  (%swap2_dec_bound_three _1 _2 _3 _4))))
; %swap2_dec_bound_three bb6
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_4 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _4) (~cur<~Mut<~Mut<Int>>> _4)) (= (~ret<~Mut<~Mut<Int>>> _3) (~cur<~Mut<~Mut<Int>>> _3)) true)
  (%swap2_dec_bound_three.6 _1 _2 _3 _4 0))))
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_4 ~Mut<~Mut<~Mut<Int>>>) (_23 Int) (_*.8_11 ~Mut<~Mut<Int>>) (_*.8_13 ~Mut<~Mut<Int>>) (_*.8_15 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_bound_three (- _1 1) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) 1) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) _*.8_11) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) 2) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) _*.8_13) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _4))) 3) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _4)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _4))) _*.8_15)) (= (~ret<~Mut<~Mut<Int>>> _4) _*.8_15) (= (~ret<~Mut<~Mut<Int>>> _3) _*.8_13) (= (~ret<~Mut<~Mut<Int>>> _2) _*.8_11) (distinct _23 0) true)
  (%swap2_dec_bound_three.6 _1 _2 _3 _4 _23))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
