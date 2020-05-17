(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %inc_max_three (~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %inc_max_three.0 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %inc_max_three.4 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %inc_max_three.8 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %inc_max_three_repeat (Int ~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %inc_max_three_repeat.0 (Int ~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.9 (Int Int Int Int Bool Bool) Bool)

; %inc_max_three
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (%inc_max_three.0 _1 _2 _3 (< (~cur<Int> _1) (~cur<Int> _2))))
  (%inc_max_three _1 _2 _3))))
; %inc_max_three bb0
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (%inc_max_three.4 _1 _2 _3 (< (~cur<Int> _2) (~cur<Int> _3))))
  (%inc_max_three.0 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_*.2_3 ~Mut<Int>) (_*.2_4 ~Mut<Int>) (_*.2_7 ~Mut<Int>) (_*.2_8 ~Mut<Int>)) (=>
  (and (= _*.2_8 _1) (= _*.2_4 _2) (= _*.2_7 _*.2_8) (= _*.2_3 _*.2_4) (%inc_max_three.4 _*.2_3 _*.2_7 _3 (< (~cur<Int> _*.2_7) (~cur<Int> _3))))
  (%inc_max_three.0 _1 _2 _3 true))))
; %inc_max_three bb4
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (%inc_max_three.8 _1 _2 _3 (< (~cur<Int> _1) (~cur<Int> _2))))
  (%inc_max_three.4 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_*.6_3 ~Mut<Int>) (_*.6_4 ~Mut<Int>) (_*.6_7 ~Mut<Int>) (_*.6_8 ~Mut<Int>)) (=>
  (and (= _*.6_8 _2) (= _*.6_4 _3) (= _*.6_7 _*.6_8) (= _*.6_3 _*.6_4) (%inc_max_three.8 _1 _*.6_3 _*.6_7 (< (~cur<Int> _1) (~cur<Int> _*.6_3))))
  (%inc_max_three.4 _1 _2 _3 true))))
; %inc_max_three bb8
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _2) (+ (~cur<Int> _2) 1)) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _1) (+ (~cur<Int> _1) 2)) true)
  (%inc_max_three.8 _1 _2 _3 false))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_*.10_3 ~Mut<Int>) (_*.10_4 ~Mut<Int>) (_*.10_7 ~Mut<Int>) (_*.10_8 ~Mut<Int>)) (=>
  (and (= _*.10_8 _1) (= _*.10_4 _2) (= _*.10_7 _*.10_8) (= _*.10_3 _*.10_4) (= (~ret<Int> _*.10_7) (+ (~cur<Int> _*.10_7) 1)) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _*.10_3) (+ (~cur<Int> _*.10_3) 2)) true)
  (%inc_max_three.8 _1 _2 _3 true))))

; %inc_max_three_repeat
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>)) (=>
  (and (%inc_max_three_repeat.0 _1 _2 _3 _4 (not (= _1 0))))
  (%inc_max_three_repeat _1 _2 _3 _4))))
; %inc_max_three_repeat bb0
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<Int> _2) (~cur<Int> _2)) true)
  (%inc_max_three_repeat.0 _1 _2 _3 _4 false))))
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>) (_*.2_2 Int) (_*.2_4 Int) (_*.2_6 Int) (_*.3_11 Int) (_*.3_13 Int) (_*.3_15 Int)) (=>
  (and (%inc_max_three (~mut<Int> (~cur<Int> _2) _*.2_2) (~mut<Int> (~cur<Int> _3) _*.2_4) (~mut<Int> (~cur<Int> _4) _*.2_6)) (%inc_max_three_repeat (- _1 1) (~mut<Int> _*.2_2 _*.3_11) (~mut<Int> _*.2_4 _*.3_13) (~mut<Int> _*.2_6 _*.3_15)) (= (~ret<Int> _3) _*.3_13) (= (~ret<Int> _4) _*.3_15) (= (~ret<Int> _2) _*.3_11) true)
  (%inc_max_three_repeat.0 _1 _2 _3 _4 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_?.3 Int) (_*.4_5 Int) (_*.4_6 Int) (_*.4_9 Int) (_*.4_10 Int) (_*.4_13 Int) (_*.4_14 Int)) (=>
  (and (%inc_max_three_repeat _?.0 (~mut<Int> _?.1 _*.4_6) (~mut<Int> _?.2 _*.4_10) (~mut<Int> _?.3 _*.4_14)) (= _*.4_13 _*.4_14) (= _*.4_9 _*.4_10) (= _*.4_5 _*.4_6) (%main.5 _?.0 _*.4_5 _*.4_9 _*.4_13 (>= (- _*.4_5 _*.4_9) _?.0) _!))
  (%main _!))))
; %main bb5
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 _4 false (>= (- _3 _2) _1) _!))
  (%main.5 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 (not true) _!))
  (%main.5 _1 _2 _3 _4 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 (not false) _!))
  (%main.8 _1 _2 _3 _4 _15 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.9 _1 _2 _3 _4 (not true) _!))
  (%main.8 _1 _2 _3 _4 _15 true _!))))
; %main bb9
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.9 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.9 _1 _2 _3 _4 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
