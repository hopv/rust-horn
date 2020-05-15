(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))
(declare-datatypes ((~Mut<~Mut<~Mut<Int>>> 0)) ((par () ((~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>) (~ret<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>> (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>>.1 (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)
(declare-fun %swap2_dec_bound (Int ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %swap2_dec_bound.2 (Int ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_9 Int) (_*.3_10 ~Mut<Int>) (_*.3_11 ~Mut<~Mut<Int>>) (_*.3_12 ~Mut<~Mut<Int>>) (_*.3_17 Int) (_*.3_18 ~Mut<Int>) (_*.3_19 ~Mut<~Mut<Int>>) (_*.3_20 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_bound _?.0 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.3_9) _*.3_10) _*.3_12) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.2 _*.3_17) _*.3_18) _*.3_20)) (= (~ret<Int> _*.3_18) (~cur<Int> _*.3_18)) (= (~ret<~Mut<Int>> _*.3_19) (~cur<~Mut<Int>> _*.3_19)) (= _*.3_19 _*.3_20) (= (~ret<Int> _*.3_10) (~cur<Int> _*.3_10)) (= (~ret<~Mut<Int>> _*.3_11) (~cur<~Mut<Int>> _*.3_11)) (= _*.3_11 _*.3_12) (%main.4 _?.0 _*.3_9 _*.3_17 _?.1 (>= _?.1 _*.3_9) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not false) _!))
  (%main.4 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 _4 true (<= (- _4 _2) (* 2 _1)) _!))
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
  (and (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.3_2 ~Mut<Int>) (_*.3_4 ~Mut<Int>)) (=>
  (and (= _*.3_4 (~cur<~Mut<Int>> _1)) (= _*.3_2 (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _1) _*.3_2) (= (~ret<~Mut<Int>> _2) _*.3_4) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 true))))

; %may_swap<~Mut<~Mut<Int>>>
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<~Mut<Int>>> _1 _2))))
; %may_swap<~Mut<~Mut<Int>>> bb1
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_*.3_2 ~Mut<~Mut<Int>>) (_*.3_4 ~Mut<~Mut<Int>>)) (=>
  (and (= _*.3_4 (~cur<~Mut<~Mut<Int>>> _1)) (= _*.3_2 (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _1) _*.3_2) (= (~ret<~Mut<~Mut<Int>>> _2) _*.3_4) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 true))))

; %swap2_dec_bound
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_*.0_2 ~Mut<~Mut<Int>>) (_*.0_4 ~Mut<~Mut<Int>>) (_*.1_5 ~Mut<Int>) (_*.1_7 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _2) _*.0_2) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _3) _*.0_4)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.0_2) _*.1_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.0_4) _*.1_7)) (%swap2_dec_bound.2 _1 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.1_5 (~ret<~Mut<Int>> _*.0_2)) (~ret<~Mut<~Mut<Int>>> _2)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.1_7 (~ret<~Mut<Int>> _*.0_4)) (~ret<~Mut<~Mut<Int>>> _3)) (= _1 0)))
  (%swap2_dec_bound _1 _2 _3))))
; %swap2_dec_bound bb2
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_*.3_10 ~Mut<~Mut<Int>>) (_*.3_12 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_bound (- _1 1) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) 1) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) _*.3_10) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) 2) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) _*.3_12)) (= (~ret<~Mut<~Mut<Int>>> _3) _*.3_12) (= (~ret<~Mut<~Mut<Int>>> _2) _*.3_10) true)
  (%swap2_dec_bound.2 _1 _2 _3 false))))
(assert (forall ((_1 Int) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _3) (~cur<~Mut<~Mut<Int>>> _3)) (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) true)
  (%swap2_dec_bound.2 _1 _2 _3 true))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
