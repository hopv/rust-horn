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
(declare-fun %swap2_dec_three (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %swap2_dec_three.7 (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_7 Int) (_*.3_8 ~Mut<Int>) (_*.3_9 ~Mut<~Mut<Int>>) (_*.3_10 ~Mut<~Mut<Int>>) (_*.3_15 Int) (_*.3_16 ~Mut<Int>) (_*.3_17 ~Mut<~Mut<Int>>) (_*.3_18 ~Mut<~Mut<Int>>) (_*.3_23 Int) (_*.3_24 ~Mut<Int>) (_*.3_25 ~Mut<~Mut<Int>>) (_*.3_26 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_three (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.0 _*.3_7) _*.3_8) _*.3_10) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.3_15) _*.3_16) _*.3_18) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.2 _*.3_23) _*.3_24) _*.3_26)) (= (~ret<Int> _*.3_24) (~cur<Int> _*.3_24)) (= (~ret<~Mut<Int>> _*.3_25) (~cur<~Mut<Int>> _*.3_25)) (= _*.3_25 _*.3_26) (= (~ret<Int> _*.3_16) (~cur<Int> _*.3_16)) (= (~ret<~Mut<Int>> _*.3_17) (~cur<~Mut<Int>> _*.3_17)) (= _*.3_17 _*.3_18) (= (~ret<Int> _*.3_8) (~cur<Int> _*.3_8)) (= (~ret<~Mut<Int>> _*.3_9) (~cur<~Mut<Int>> _*.3_9)) (= _*.3_9 _*.3_10) (%main.4 _*.3_7 _*.3_15 _*.3_23 _?.0 (>= _?.0 _*.3_7) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not false) _!))
  (%main.4 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 _4 true (<= (- _4 _1) 3) _!))
  (%main.4 _1 _2 _3 _4 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_20 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not false) _!))
  (%main.7 _1 _2 _3 _4 _20 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_20 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 (not true) _!))
  (%main.7 _1 _2 _3 _4 _20 true _!))))
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
  (and (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_*.3_2 ~Mut<~Mut<Int>>) (_*.3_4 ~Mut<~Mut<Int>>)) (=>
  (and (= _*.3_4 (~cur<~Mut<~Mut<Int>>> _1)) (= _*.3_2 (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _2) _*.3_4) (= (~ret<~Mut<~Mut<Int>>> _1) _*.3_2) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 true))))

; %swap2_dec_three
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_?.6 Bool) (_*.0_2 ~Mut<~Mut<Int>>) (_*.0_4 ~Mut<~Mut<Int>>) (_*.1_5 ~Mut<~Mut<Int>>) (_*.1_7 ~Mut<~Mut<Int>>) (_*.2_5 ~Mut<~Mut<Int>>) (_*.2_7 ~Mut<~Mut<Int>>) (_*.3_5 ~Mut<Int>) (_*.3_7 ~Mut<Int>) (_*.4_5 ~Mut<Int>) (_*.4_7 ~Mut<Int>) (_*.5_5 ~Mut<Int>) (_*.5_7 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _1) _*.0_2) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _2) _*.0_4)) (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> _*.0_4 _*.1_5) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _3) _*.1_7)) (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> _*.0_2 _*.2_5) (~mut<~Mut<~Mut<Int>>> _*.1_5 _*.2_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.2_5) _*.3_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.2_7) _*.3_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.3_7 _*.4_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.1_7) _*.4_7)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> _*.3_5 _*.5_5) (~mut<~Mut<Int>> _*.4_5 _*.5_7)) (%swap2_dec_three.7 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.5_5 (~ret<~Mut<Int>> _*.2_5)) (~ret<~Mut<~Mut<Int>>> _1)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.5_7 (~ret<~Mut<Int>> _*.2_7)) (~ret<~Mut<~Mut<Int>>> _2)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.4_7 (~ret<~Mut<Int>> _*.1_7)) (~ret<~Mut<~Mut<Int>>> _3)) _?.6))
  (%swap2_dec_three _1 _2 _3))))
; %swap2_dec_three bb7
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>) (_*.8_6 ~Mut<~Mut<Int>>) (_*.8_8 ~Mut<~Mut<Int>>) (_*.8_10 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec_three (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1))) 1) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1))) _*.8_6) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) 2) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) _*.8_8) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) 3) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _3))) _*.8_10)) (= (~ret<~Mut<~Mut<Int>>> _2) _*.8_8) (= (~ret<~Mut<~Mut<Int>>> _3) _*.8_10) (= (~ret<~Mut<~Mut<Int>>> _1) _*.8_6) true)
  (%swap2_dec_three.7 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_3 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _3) (~cur<~Mut<~Mut<Int>>> _3)) (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) true)
  (%swap2_dec_three.7 _1 _2 _3 true))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
