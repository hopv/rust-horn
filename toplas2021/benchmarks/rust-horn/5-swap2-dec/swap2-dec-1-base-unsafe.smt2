(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))
(declare-datatypes ((~Mut<~Mut<Int>> 0)) ((par () ((~mut<~Mut<Int>> (~cur<~Mut<Int>> ~Mut<Int>) (~ret<~Mut<Int>> ~Mut<Int>))))))
(declare-datatypes ((~Mut<~Mut<~Mut<Int>>> 0)) ((par () ((~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>) (~ret<~Mut<~Mut<Int>>> ~Mut<~Mut<Int>>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.3 (Int Int Int Bool Bool) Bool)
(declare-fun %main.6 (Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Bool Bool) Bool)
(declare-fun %may_swap<~Mut<Int>> (~Mut<~Mut<Int>> ~Mut<~Mut<Int>>) Bool)
(declare-fun %may_swap<~Mut<Int>>.1 (~Mut<~Mut<Int>> ~Mut<~Mut<Int>> Bool) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>> (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %may_swap<~Mut<~Mut<Int>>>.1 (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)
(declare-fun %swap2_dec (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>>) Bool)
(declare-fun %swap2_dec.3 (~Mut<~Mut<~Mut<Int>>> ~Mut<~Mut<~Mut<Int>>> Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_*.2_7 Int) (_*.2_8 ~Mut<Int>) (_*.2_9 ~Mut<~Mut<Int>>) (_*.2_10 ~Mut<~Mut<Int>>) (_*.2_15 Int) (_*.2_16 ~Mut<Int>) (_*.2_17 ~Mut<~Mut<Int>>) (_*.2_18 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.0 _*.2_7) _*.2_8) _*.2_10) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> _?.1 _*.2_15) _*.2_16) _*.2_18)) (= (~ret<Int> _*.2_16) (~cur<Int> _*.2_16)) (= (~ret<~Mut<Int>> _*.2_17) (~cur<~Mut<Int>> _*.2_17)) (= _*.2_17 _*.2_18) (= (~ret<Int> _*.2_8) (~cur<Int> _*.2_8)) (= (~ret<~Mut<Int>> _*.2_9) (~cur<~Mut<Int>> _*.2_9)) (= _*.2_9 _*.2_10) (%main.3 _*.2_7 _*.2_15 _?.0 (>= _?.0 _*.2_7) _!))
  (%main _!))))
; %main bb3
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.3 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.6 _1 _2 _3 true (<= (- _3 _1) 3) _!))
  (%main.3 _1 _2 _3 true _!))))
; %main bb6
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not false) _!))
  (%main.6 _1 _2 _3 _15 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 (not true) _!))
  (%main.6 _1 _2 _3 _15 true _!))))
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
  (and (= (~ret<~Mut<Int>> _1) (~cur<~Mut<Int>> _1)) (= (~ret<~Mut<Int>> _2) (~cur<~Mut<Int>> _2)) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<Int>>) (_2 ~Mut<~Mut<Int>>) (_*.2_2 ~Mut<Int>) (_*.2_4 ~Mut<Int>)) (=>
  (and (= _*.2_4 (~cur<~Mut<Int>> _1)) (= _*.2_2 (~cur<~Mut<Int>> _2)) (= (~ret<~Mut<Int>> _1) _*.2_2) (= (~ret<~Mut<Int>> _2) _*.2_4) true)
  (%may_swap<~Mut<Int>>.1 _1 _2 true))))

; %may_swap<~Mut<~Mut<Int>>>
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_?.0 Bool)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 _?.0))
  (%may_swap<~Mut<~Mut<Int>>> _1 _2))))
; %may_swap<~Mut<~Mut<Int>>> bb1
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_*.2_2 ~Mut<~Mut<Int>>) (_*.2_4 ~Mut<~Mut<Int>>)) (=>
  (and (= _*.2_4 (~cur<~Mut<~Mut<Int>>> _1)) (= _*.2_2 (~cur<~Mut<~Mut<Int>>> _2)) (= (~ret<~Mut<~Mut<Int>>> _1) _*.2_2) (= (~ret<~Mut<~Mut<Int>>> _2) _*.2_4) true)
  (%may_swap<~Mut<~Mut<Int>>>.1 _1 _2 true))))

; %swap2_dec
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_?.2 Bool) (_*.0_2 ~Mut<~Mut<Int>>) (_*.0_4 ~Mut<~Mut<Int>>) (_*.1_5 ~Mut<Int>) (_*.1_7 ~Mut<Int>)) (=>
  (and (%may_swap<~Mut<~Mut<Int>>> (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _1) _*.0_2) (~mut<~Mut<~Mut<Int>>> (~cur<~Mut<~Mut<Int>>> _2) _*.0_4)) (%may_swap<~Mut<Int>> (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.0_2) _*.1_5) (~mut<~Mut<Int>> (~cur<~Mut<Int>> _*.0_4) _*.1_7)) (%swap2_dec.3 (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.1_5 (~ret<~Mut<Int>> _*.0_2)) (~ret<~Mut<~Mut<Int>>> _1)) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> _*.1_7 (~ret<~Mut<Int>> _*.0_4)) (~ret<~Mut<~Mut<Int>>> _2)) _?.2))
  (%swap2_dec _1 _2))))
; %swap2_dec bb3
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>) (_*.5_5 ~Mut<~Mut<Int>>) (_*.5_7 ~Mut<~Mut<Int>>)) (=>
  (and (%swap2_dec (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1))) 1) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _1))) _*.5_5) (~mut<~Mut<~Mut<Int>>> (~mut<~Mut<Int>> (~mut<Int> (- (~cur<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) 2) (~ret<Int> (~cur<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2)))) (~ret<~Mut<Int>> (~cur<~Mut<~Mut<Int>>> _2))) _*.5_7)) (= (~ret<~Mut<~Mut<Int>>> _1) _*.5_5) (= (~ret<~Mut<~Mut<Int>>> _2) _*.5_7) true)
  (%swap2_dec.3 _1 _2 false))))
(assert (forall ((_1 ~Mut<~Mut<~Mut<Int>>>) (_2 ~Mut<~Mut<~Mut<Int>>>)) (=>
  (and (= (~ret<~Mut<~Mut<Int>>> _1) (~cur<~Mut<~Mut<Int>>> _1)) (= (~ret<~Mut<~Mut<Int>>> _2) (~cur<~Mut<~Mut<Int>>> _2)) true)
  (%swap2_dec.3 _1 _2 true))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
