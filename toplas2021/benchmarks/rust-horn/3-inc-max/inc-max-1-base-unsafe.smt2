(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.3 (Int Int ~Mut<Int> Bool Bool) Bool)
(declare-fun %take_max (~Mut<Int> ~Mut<Int> ~Mut<Int>) Bool)
(declare-fun %take_max.0 (~Mut<Int> ~Mut<Int> Bool ~Mut<Int>) Bool)

; %main
(assert (forall ((_! Bool) (_@.2 ~Mut<Int>) (_?.0 Int) (_?.1 Int) (_*.2_3 Int) (_*.2_4 Int) (_*.2_7 Int) (_*.2_8 Int)) (=>
  (and (%take_max (~mut<Int> _?.0 _*.2_4) (~mut<Int> _?.1 _*.2_8) _@.2) (= _*.2_7 _*.2_8) (= _*.2_3 _*.2_4) (%main.3 _*.2_3 _*.2_7 (~mut<Int> (+ (~cur<Int> _@.2) 1) (~ret<Int> _@.2)) (not (not (= _*.2_3 (+ _*.2_7 1)))) _!))
  (%main _!))))
; %main bb3
(assert (forall ((_1 Int) (_2 Int) (_3 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= _! false))
  (%main.3 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= _! true))
  (%main.3 _1 _2 _3 true _!))))

; %take_max
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>)) (=>
  (and (%take_max.0 _1 _2 (>= (~cur<Int> _1) (~cur<Int> _2)) _@))
  (%take_max _1 _2 _@))))
; %take_max bb0
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>) (_*.1_1 Int) (_*.1_2 Int) (_*.3_0 Int) (_*.3_1 Int)) (=>
  (and (= _*.1_1 _*.1_2) (= _*.1_2 _*.3_0) (= _*.3_0 _*.3_1) (= (~ret<Int> _2) _*.1_1) (= (~ret<Int> _1) (~cur<Int> _1)) (= _@ (~mut<Int> (~cur<Int> _2) _*.3_1)))
  (%take_max.0 _1 _2 false _@))))
(assert (forall ((_1 ~Mut<Int>) (_2 ~Mut<Int>) (_@ ~Mut<Int>) (_*.2_1 Int) (_*.2_2 Int) (_*.3_0 Int) (_*.3_1 Int)) (=>
  (and (= _*.2_1 _*.2_2) (= _*.2_2 _*.3_0) (= _*.3_0 _*.3_1) (= (~ret<Int> _2) (~cur<Int> _2)) (= (~ret<Int> _1) _*.2_1) (= _@ (~mut<Int> (~cur<Int> _1) _*.3_1)))
  (%take_max.0 _1 _2 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
