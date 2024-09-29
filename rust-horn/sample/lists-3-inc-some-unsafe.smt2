(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))
(declare-datatypes ((%std/alloc/Global 0)) ((par () (
  %std/alloc/Global-0))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (%List Int ~Mut<Int> Int Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)
(declare-fun %take_some (~Mut<%List> ~Mut<Int>) Bool)
(declare-fun %take_some.0 (~Mut<%List> ~Mut<Int>) Bool)
(declare-fun %take_some.5 (~Mut<%List> ~Mut<Int> ~Mut<%List> Bool ~Mut<Int>) Bool)

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_@.2 ~Mut<Int>) (_@.3 Int) (_?.0 %List) (_*.2_6 %List) (_*.2_7 %List)) (=>
  (and (%sum _?.0 _@.1) (%take_some (~mut<%List> _?.0 _*.2_7) _@.2) (= _*.2_6 _*.2_7) (%sum _*.2_6 _@.3) (%main.4 _*.2_6 _@.1 (~mut<Int> (+ (~cur<Int> _@.2) 1) (~ret<Int> _@.2)) _@.3 (> _@.3 (+ _@.1 1)) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 %List) (_2 Int) (_5 ~Mut<Int>) (_8 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _5) (~cur<Int> _5)) (= _! true))
  (%main.4 _1 _2 _5 _8 false _!))))
(assert (forall ((_1 %List) (_2 Int) (_5 ~Mut<Int>) (_8 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _5) (~cur<Int> _5)) (= _! false))
  (%main.4 _1 _2 _5 _8 true _!))))

; %sum
(assert (forall ((_1 %List) (_@ Int)) (=>
  (and (%sum.0 _1 _@))
  (%sum _1 _@))))
; %sum bb0
(assert (forall ((_@ Int) (_@.4 Int) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%sum _$.0_0/1 _@.4) (= _@ (+ _$.0_0/0 _@.4)))
  (%sum.0 (%List-0 _$.0_0/0 _$.0_0/1) _@))))
(assert (forall ((_@ Int)) (=>
  (and (= _@ 0))
  (%sum.0 %List-1 _@))))

; %take_some
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>)) (=>
  (and (%take_some.0 _1 _@))
  (%take_some _1 _@))))
; %take_some bb0
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>) (_?.4 Bool) (_*.4_1 Int) (_*.4_3 %List) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%take_some.5 (~mut<%List> (%List-0 _*.4_1 _*.4_3) (~ret<%List> _1)) (~mut<Int> _$.0_0/0 _*.4_1) (~mut<%List> _$.0_0/1 _*.4_3) _?.4 _@))
  (%take_some.0 (~mut<%List> (%List-0 _$.0_0/0 _$.0_0/1) (~ret<%List> _1)) _@))))
(assert (forall ((_1 ~Mut<%List>) (_@ ~Mut<Int>) (_@.3 ~Mut<Int>) (_*.3_2 %List) (_*.10_0 Int) (_*.11_0 Int) (_*.11_1 Int)) (=>
  (and (%take_some (~mut<%List> %List-1 _*.3_2) _@.3) (= (~ret<Int> _@.3) _*.10_0) (= _*.10_0 _*.11_0) (= _*.11_0 _*.11_1) (= (~ret<%List> _1) _*.3_2) (= _@ (~mut<Int> (~cur<Int> _@.3) _*.11_1)))
  (%take_some.0 (~mut<%List> %List-1 (~ret<%List> _1)) _@))))
; %take_some bb5
(assert (forall ((_1 ~Mut<%List>) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_@ ~Mut<Int>) (_@.7 ~Mut<Int>) (_*.7_2 %List) (_*.8_0 Int) (_*.9_0 Int) (_*.9_2 Int) (_*.11_0 Int) (_*.11_1 Int)) (=>
  (and (%take_some (~mut<%List> (~cur<%List> _6) _*.7_2) _@.7) (= (~ret<Int> _@.7) _*.8_0) (= _*.8_0 _*.9_0) (= _*.9_0 _*.9_2) (= (~ret<%List> _6) _*.7_2) (= (~ret<Int> _5) (~cur<Int> _5)) (= _*.9_2 _*.11_0) (= _*.11_0 _*.11_1) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ (~mut<Int> (~cur<Int> _@.7) _*.11_1)))
  (%take_some.5 _1 _5 _6 false _@))))
(assert (forall ((_1 ~Mut<%List>) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_@ ~Mut<Int>) (_*.6_1 Int) (_*.6_2 Int) (_*.9_0 Int) (_*.9_2 Int) (_*.11_0 Int) (_*.11_1 Int)) (=>
  (and (= _*.6_1 _*.6_2) (= _*.6_2 _*.9_0) (= _*.9_0 _*.9_2) (= (~ret<%List> _6) (~cur<%List> _6)) (= (~ret<Int> _5) _*.6_1) (= _*.9_2 _*.11_0) (= _*.11_0 _*.11_1) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ (~mut<Int> (~cur<Int> _5) _*.11_1)))
  (%take_some.5 _1 _5 _6 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
