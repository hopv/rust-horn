(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %swap_dec_bound (Int ~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %swap_dec_bound.1 (Int ~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Int) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_8 Int) (_*.3_9 ~Mut<Int>) (_*.3_10 ~Mut<Int>) (_*.3_14 Int) (_*.3_15 ~Mut<Int>) (_*.3_16 ~Mut<Int>)) (=>
  (and (%swap_dec_bound _?.0 (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.3_8) _*.3_10) (~mut<~Mut<Int>> (~mut<Int> _?.2 _*.3_14) _*.3_16)) (= (~ret<Int> _*.3_15) (~cur<Int> _*.3_15)) (= _*.3_15 _*.3_16) (= (~ret<Int> _*.3_9) (~cur<Int> _*.3_9)) (= _*.3_9 _*.3_10) (%main.4 _?.0 _*.3_8 _*.3_14 _?.1 (>= _?.1 _*.3_8) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 _4 (not false) _!))
  (%main.4 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 _4 (not (< (- _4 _2) (* 2 _1))) _!))
  (%main.4 _1 _2 _3 _4 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.7 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.7 _1 _2 _3 _4 true _!))))

; %may_swap<~Mut<Int>>
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<Int>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<Int>> _1 _2))))
; %may_swap<~Mut<Int>> bb1
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.2_2 ~Mut<Int>) (_*.2_4 ~Mut<Int>)) (=>
  (and (= _*.2_4 (~cur<~Mut<Int>> _1)) (= _*.2_2 (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _1) _*.2_2) (= (~ret<~Mut<Int>> _2) _*.2_4) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 true))))

; %swap_dec_bound
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>) (_*.0_2 ~Mut<Int>) (_*.0_4 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _2) _*.0_2) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _3) _*.0_4)) (%swap_dec_bound.1 _1 (~mut<~Mut<Int>> _*.0_2 (~ret<~Mut<Int>> _2)) (~mut<~Mut<Int>> _*.0_4 (~ret<~Mut<Int>> _3)) _1))
  (%swap_dec_bound _1 _2 _3))))
; %swap_dec_bound bb1
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>)) (=>
  (and (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _3) (~cur<~Mut<Int>> _3)) true)
  (%swap_dec_bound.1 _1 _2 _3 0))))
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<Int>>) (_3 ~Mut<~Mut<Int>>) (_7 Int) (_*.3_10 ~Mut<Int>) (_*.3_12 ~Mut<Int>)) (=>
  (and (%swap_dec_bound (- _1 1) (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _2)) 1) (~ret<Int> (~cur<~Mut<Int>> _2))) _*.3_10) (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> _3)) 2) (~ret<Int> (~cur<~Mut<Int>> _3))) _*.3_12)) (= (~ret<~Mut<Int>> _2) _*.3_10) (= (~ret<~Mut<Int>> _3) _*.3_12) (distinct _7 0) true)
  (%swap_dec_bound.1 _1 _2 _3 _7))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
