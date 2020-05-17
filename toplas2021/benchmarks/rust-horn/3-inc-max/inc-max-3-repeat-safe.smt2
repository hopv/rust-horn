(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %inc_max_repeat (Int ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %inc_max_repeat.0 (Int ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (Int Int Int Bool Bool) Bool)
(declare-fun %main.7 (Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Bool Bool) Bool)
(declare-fun %take_max (~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %take_max.0 (~Mut<Int> ~Mut<Int> Bool ~Mut<Int>) Bool)

; %inc_max_repeat
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (%inc_max_repeat.0 _1 _2 _3 (not (= _1 0))))
  (%inc_max_repeat _1 _2 _3))))
; %inc_max_repeat bb0
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<Int> _2) (~cur<Int> _2)) true)
  (%inc_max_repeat.0 _1 _2 _3 false))))
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@.2 ~Mut<Int>) (_*.2_2 Int) (_*.2_4 Int) (_*.3_10 Int) (_*.3_12 Int)) (=>
  (and (%take_max (~mut<Int> (~cur<Int> _2) _*.2_2) (~mut<Int> (~cur<Int> _3) _*.2_4) _@.2) (%inc_max_repeat (- _1 1) (~mut<Int> _*.2_2 _*.3_10) (~mut<Int> _*.2_4 _*.3_12)) (= (~ret<Int> _@.2) (+ (~cur<Int> _@.2) 1)) (= (~ret<Int> _2) _*.3_10) (= (~ret<Int> _3) _*.3_12) true)
  (%inc_max_repeat.0 _1 _2 _3 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_?.1 Int) (_?.2 Int) (_*.3_5 Int) (_*.3_6 Int) (_*.3_9 Int) (_*.3_10 Int)) (=>
  (and (%inc_max_repeat _?.0 (~mut<Int> _?.1 _*.3_6) (~mut<Int> _?.2 _*.3_10)) (= _*.3_9 _*.3_10) (= _*.3_5 _*.3_6) (%main.4 _?.0 _*.3_5 _*.3_9 (>= (- _*.3_5 _*.3_9) _?.0) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.7 _1 _2 _3 false (>= (- _3 _2) _1) _!))
  (%main.4 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 (not true) _!))
  (%main.4 _1 _2 _3 true _!))))
; %main bb7
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_12 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 (not false) _!))
  (%main.7 _1 _2 _3 _12 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_12 Bool) (_! Bool)) (=>
  (and (%main.8 _1 _2 _3 (not true) _!))
  (%main.7 _1 _2 _3 _12 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.8 _1 _2 _3 true _!))))

; %take_max
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>)) (=>
  (and (%take_max.0 _1 _2 (>= (~cur<Int> _1) (~cur<Int> _2)) _@))
  (%take_max _1 _2 _@))))
; %take_max bb0
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>) (_*.1_1 Int) (_*.1_2 Int) (_*.3_0 Int) (_*.3_1 Int)) (=>
  (and (= _*.1_1 _*.1_2) (= _*.1_2 _*.3_0) (= _*.3_0 _*.3_1) (= (~ret<Int> _1) (~cur<Int> _1)) (= (~ret<Int> _2) _*.1_1) (= _@ (~mut<Int> (~cur<Int> _2) _*.3_1)))
  (%take_max.0 _1 _2 false _@))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>) (_*.2_1 Int) (_*.2_2 Int) (_*.3_0 Int) (_*.3_1 Int)) (=>
  (and (= _*.2_1 _*.2_2) (= _*.2_2 _*.3_0) (= _*.3_0 _*.3_1) (= (~ret<Int> _1) _*.2_1) (= (~ret<Int> _2) (~cur<Int> _2)) (= _@ (~mut<Int> (~cur<Int> _1) _*.3_1)))
  (%take_max.0 _1 _2 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
