(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %inc_max_three (~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %inc_max_three.0 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %inc_max_three.4 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %inc_max_three.8 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Int Int Int Bool Bool) Bool)

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
  (and (= _*.10_8 _1) (= _*.10_4 _2) (= _*.10_7 _*.10_8) (= _*.10_3 _*.10_4) (= (~ret<Int> _*.10_3) (+ (~cur<Int> _*.10_3) 2)) (= (~ret<Int> _*.10_7) (+ (~cur<Int> _*.10_7) 1)) (= (~ret<Int> _3) (~cur<Int> _3)) true)
  (%inc_max_three.8 _1 _2 _3 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_3 Int) (_*.3_4 Int) (_*.3_7 Int) (_*.3_8 Int) (_*.3_11 Int) (_*.3_12 Int)) (=>
  (and (%inc_max_three (~mut<Int> _?.0 _*.3_4) (~mut<Int> _?.1 _*.3_8) (~mut<Int> _?.2 _*.3_12)) (= _*.3_11 _*.3_12) (= _*.3_7 _*.3_8) (= _*.3_3 _*.3_4) (%main.4 _*.3_3 _*.3_7 _*.3_11 (not (not (= _*.3_3 _*.3_7))) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.4 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.4 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
