(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-datatypes ((~Tup<~Mut<Int>-~Mut<Int>> 0)) ((par () ((~tup<~Mut<Int>-~Mut<Int>> (~at0/<~Mut<Int>-~Mut<Int>> ~Mut<Int>) (~at1/<~Mut<Int>-~Mut<Int>> ~Mut<Int>))))))

(declare-fun %inc_max_three_repeat (Int ~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %inc_max_three_repeat.0 (Int ~Mut<Int> ~Mut<Int> ~Mut<Int> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (Int Int Int Int Bool Bool) Bool)
(declare-fun %main.8 (Int Int Int Int Bool Bool Bool) Bool)
(declare-fun %main.9 (Bool Bool) Bool)
(declare-fun %max_mid (~Mut<Int> ~Mut<Int> ~Mut<Int> ~Tup<~Mut<Int>-~Mut<Int>>) Bool)
(declare-fun %max_mid.0 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool ~Tup<~Mut<Int>-~Mut<Int>>) Bool)
(declare-fun %max_mid.3 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool ~Tup<~Mut<Int>-~Mut<Int>>) Bool)
(declare-fun %max_mid.6 (~Mut<Int> ~Mut<Int> ~Mut<Int> Bool ~Tup<~Mut<Int>-~Mut<Int>>) Bool)

; %inc_max_three_repeat
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>)) (=>
  (and (%inc_max_three_repeat.0 _1 _2 _3 _4 (= _1 0)))
  (%inc_max_three_repeat _1 _2 _3 _4))))
; %inc_max_three_repeat bb0
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>) (_@.1 ~Tup<~Mut<Int>-~Mut<Int>>) (_*.1_3 Int) (_*.1_5 Int) (_*.1_7 Int) (_*.4_17 Int) (_*.4_19 Int) (_*.4_21 Int)) (=>
  (and (%max_mid (~mut<Int> (~cur<Int> _2) _*.1_3) (~mut<Int> (~cur<Int> _3) _*.1_5) (~mut<Int> (~cur<Int> _4) _*.1_7) _@.1) (%inc_max_three_repeat (- _1 1) (~mut<Int> _*.1_3 _*.4_17) (~mut<Int> _*.1_5 _*.4_19) (~mut<Int> _*.1_7 _*.4_21)) (= (~ret<Int> (~at1/<~Mut<Int>-~Mut<Int>> _@.1)) (+ (~cur<Int> (~at1/<~Mut<Int>-~Mut<Int>> _@.1)) 1)) (= (~ret<Int> (~at0/<~Mut<Int>-~Mut<Int>> _@.1)) (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<Int>> _@.1)) 2)) (= (~ret<Int> _4) _*.4_21) (= (~ret<Int> _2) _*.4_17) (= (~ret<Int> _3) _*.4_19) true)
  (%inc_max_three_repeat.0 _1 _2 _3 _4 false))))
(assert (forall ((_1 Int) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_4 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<Int> _3) (~cur<Int> _3)) true)
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
  (and (%main.9 (not true) _!))
  (%main.5 _1 _2 _3 _4 true _!))))
; %main bb8
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.9 (not false) _!))
  (%main.8 _1 _2 _3 _4 _15 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 Int) (_4 Int) (_15 Bool) (_! Bool)) (=>
  (and (%main.9 (not true) _!))
  (%main.8 _1 _2 _3 _4 _15 true _!))))
; %main bb9
(assert (forall ((_! Bool)) (=>
  (and (= _! false))
  (%main.9 false _!))))
(assert (forall ((_! Bool)) (=>
  (and (= _! true))
  (%main.9 true _!))))

; %max_mid
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>)) (=>
  (and (%max_mid.0 _1 _2 _3 (> (~cur<Int> _1) (~cur<Int> _2)) _@))
  (%max_mid _1 _2 _3 _@))))
; %max_mid bb0
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>)) (=>
  (and (%max_mid.3 _1 _2 _3 (> (~cur<Int> _2) (~cur<Int> _3)) _@))
  (%max_mid.0 _1 _2 _3 false _@))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>) (_*.1_3 ~Mut<Int>) (_*.1_4 ~Mut<Int>) (_*.1_7 ~Mut<Int>) (_*.1_8 ~Mut<Int>)) (=>
  (and (= _*.1_8 _1) (= _*.1_4 _2) (= _*.1_7 _*.1_8) (= _*.1_3 _*.1_4) (%max_mid.3 _*.1_3 _*.1_7 _3 (> (~cur<Int> _*.1_7) (~cur<Int> _3)) _@))
  (%max_mid.0 _1 _2 _3 true _@))))
; %max_mid bb3
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>)) (=>
  (and (%max_mid.6 _1 _2 _3 (> (~cur<Int> _1) (~cur<Int> _2)) _@))
  (%max_mid.3 _1 _2 _3 false _@))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>) (_*.4_3 ~Mut<Int>) (_*.4_4 ~Mut<Int>) (_*.4_7 ~Mut<Int>) (_*.4_8 ~Mut<Int>)) (=>
  (and (= _*.4_8 _2) (= _*.4_4 _3) (= _*.4_7 _*.4_8) (= _*.4_3 _*.4_4) (%max_mid.6 _1 _*.4_3 _*.4_7 (> (~cur<Int> _1) (~cur<Int> _*.4_3)) _@))
  (%max_mid.3 _1 _2 _3 true _@))))
; %max_mid bb6
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>) (_*.9_2 Int) (_*.9_4 Int)) (=>
  (and (= (~ret<Int> _2) _*.9_4) (= (~ret<Int> _1) (~cur<Int> _1)) (= (~ret<Int> _3) _*.9_2) (= _@ (~tup<~Mut<Int>-~Mut<Int>> (~mut<Int> (~cur<Int> _3) _*.9_2) (~mut<Int> (~cur<Int> _2) _*.9_4))))
  (%max_mid.6 _1 _2 _3 false _@))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_3 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<Int>>) (_*.7_3 ~Mut<Int>) (_*.7_4 ~Mut<Int>) (_*.7_7 ~Mut<Int>) (_*.7_8 ~Mut<Int>) (_*.9_2 Int) (_*.9_4 Int)) (=>
  (and (= _*.7_8 _1) (= _*.7_4 _2) (= _*.7_7 _*.7_8) (= _*.7_3 _*.7_4) (= (~ret<Int> _3) _*.9_2) (= (~ret<Int> _*.7_7) _*.9_4) (= (~ret<Int> _*.7_3) (~cur<Int> _*.7_3)) (= _@ (~tup<~Mut<Int>-~Mut<Int>> (~mut<Int> (~cur<Int> _3) _*.9_2) (~mut<Int> (~cur<Int> _*.7_7) _*.9_4))))
  (%max_mid.6 _1 _2 _3 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
