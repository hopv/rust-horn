(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.6 (%List Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)
(declare-fun %take_some (~Mut<%List> ~Mut<Int>) Bool)
(declare-fun %take_some.0 (~Mut<%List> ~Mut<Int>) Bool)
(declare-fun %take_some.4 (~Mut<%List> ~Mut<Int> ~Mut<%List> Bool ~Mut<Int>) Bool)

; %main
(assert (forall ((_! Bool) (_@.2 Int) (_@.3 ~Mut<Int>) (_@.5 Int) (_?.0 %List) (_*.3_5 %List) (_*.3_6 %List)) (=>
  (and (%sum _?.0 _@.2) (%take_some (~mut<%List> _?.0 _*.3_6) _@.3) (= _*.3_5 _*.3_6) (%sum _*.3_5 _@.5) (= (~ret<Int> _@.3) (+ (~cur<Int> _@.3) 1)) (%main.6 _*.3_5 (not (= _@.5 (+ _@.2 1))) _!))
  (%main _!))))
; %main bb6
(assert (forall ((_1 %List) (_! Bool)) (=>
  (and (= _! false))
  (%main.6 _1 false _!))))
(assert (forall ((_1 %List) (_! Bool)) (=>
  (and (= _! true))
  (%main.6 _1 true _!))))

; %sum
(assert (forall ((_1 %List) (_@ Int)) (=>
  (and (%sum.0 _1 _@))
  (%sum _1 _@))))
; %sum bb0
(assert (forall ((_@ Int) (_@.3 Int) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%sum _$.0_0/1 _@.3) (= _@ (+ _$.0_0/0 _@.3)))
  (%sum.0 (%List-0 _$.0_0/0 _$.0_0/1) _@))))
(assert (forall ((_@ Int)) (=>
  (and (= _@ 0))
  (%sum.0 %List-1 _@))))

; %take_some
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>)) (=>
  (and (%take_some.0 _1 _@))
  (%take_some _1 _@))))
; %take_some bb0
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>) (_?.3 Bool) (_*.3_1 Int) (_*.3_3 %List) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%take_some.4 (~mut<%List> (%List-0 _*.3_1 _*.3_3) (~ret<%List> _1)) (~mut<Int> _$.0_0/0 _*.3_1) (~mut<%List> _$.0_0/1 _*.3_3) _?.3 _@))
  (%take_some.0 (~mut<%List> (%List-0 _$.0_0/0 _$.0_0/1) (~ret<%List> _1)) _@))))
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>) (_@.1 ~Mut<Int>) (_*.1_2 %List) (_*.9_0 Int) (_*.10_0 Int) (_*.10_1 Int)) (=>
  (and (%take_some (~mut<%List> %List-1 _*.1_2) _@.1) (= (~ret<Int> _@.1) _*.9_0) (= _*.9_0 _*.10_0) (= _*.10_0 _*.10_1) (= (~ret<%List> _1) _*.1_2) (= _@ (~mut<Int> (~cur<Int> _@.1) _*.10_1)))
  (%take_some.0 (~mut<%List> %List-1 (~ret<%List> _1)) _@))))
; %take_some bb4
(assert (forall ((_1 ~Mut<%List>) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_@ ~Mut<Int>) (_@.5 ~Mut<Int>) (_*.5_3 %List) (_*.7_0 Int) (_*.7_2 Int) (_*.8_0 Int) (_*.8_1 Int) (_*.10_0 Int) (_*.10_1 Int)) (=>
  (and (%take_some (~mut<%List> (~cur<%List> _6) _*.5_3) _@.5) (= (~ret<Int> _@.5) _*.7_0) (= _*.7_0 _*.7_2) (= _*.7_2 _*.8_0) (= _*.8_0 _*.8_1) (= (~ret<%List> _6) _*.5_3) (= (~ret<Int> _5) (~cur<Int> _5)) (= _*.8_1 _*.10_0) (= _*.10_0 _*.10_1) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ (~mut<Int> (~cur<Int> _@.5) _*.10_1)))
  (%take_some.4 _1 _5 _6 false _@))))
(assert (forall ((_1 ~Mut<%List>) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_@ ~Mut<Int>) (_*.6_1 Int) (_*.6_2 Int) (_*.8_0 Int) (_*.8_1 Int) (_*.10_0 Int) (_*.10_1 Int)) (=>
  (and (= _*.6_1 _*.6_2) (= _*.6_2 _*.8_0) (= _*.8_0 _*.8_1) (= (~ret<%List> _6) (~cur<%List> _6)) (= (~ret<Int> _5) _*.6_1) (= _*.8_1 _*.10_0) (= _*.10_0 _*.10_1) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ (~mut<Int> (~cur<Int> _5) _*.10_1)))
  (%take_some.4 _1 _5 _6 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
