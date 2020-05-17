(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-datatypes ((~Tup<~Mut<Int>-~Mut<%List>> 0)) ((par () ((~tup<~Mut<Int>-~Mut<%List>> (~at0/<~Mut<Int>-~Mut<%List>> ~Mut<Int>) (~at1/<~Mut<Int>-~Mut<%List>> ~Mut<%List>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (%List Int ~Mut<Int> ~Mut<%List> ~Mut<Int> Int Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)
(declare-fun %take_some_rest (~Mut<%List> ~Tup<~Mut<Int>-~Mut<%List>>) Bool)
(declare-fun %take_some_rest.0 (~Mut<%List> ~Tup<~Mut<Int>-~Mut<%List>>) Bool)
(declare-fun %take_some_rest.4 (~Mut<%List> ~Mut<Int> ~Mut<%List> Bool ~Tup<~Mut<Int>-~Mut<%List>>) Bool)

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_@.2 ~Tup<~Mut<Int>-~Mut<%List>>) (_@.3 ~Tup<~Mut<Int>-~Mut<%List>>) (_@.4 Int) (_?.0 %List) (_*.2_5 %List) (_*.2_6 %List) (_*.3_9 %List)) (=>
  (and (%sum _?.0 _@.1) (%take_some_rest (~mut<%List> _?.0 _*.2_6) _@.2) (= _*.2_5 _*.2_6) (%take_some_rest (~mut<%List> (~cur<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.2)) _*.3_9) _@.3) (= (~ret<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.3)) (~cur<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.3))) (%sum _*.2_5 _@.4) (%main.5 _*.2_5 _@.1 (~mut<Int> (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.2)) 1) (~ret<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.2))) (~mut<%List> _*.3_9 (~ret<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.2))) (~mut<Int> (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.3)) 1) (~ret<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.3))) _@.4 (not (= _@.4 (+ _@.1 2))) _!))
  (%main _!))))
; %main bb5
(assert (forall ((_1 %List) (_2 Int) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_10 ~Mut<Int>) (_13 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _10) (~cur<Int> _10)) (= (~ret<%List> _6) (~cur<%List> _6)) (= (~ret<Int> _5) (~cur<Int> _5)) (= _! false))
  (%main.5 _1 _2 _5 _6 _10 _13 false _!))))
(assert (forall ((_1 %List) (_2 Int) (_5 ~Mut<Int>) (_6 ~Mut<%List>) (_10 ~Mut<Int>) (_13 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _10) (~cur<Int> _10)) (= (~ret<%List> _6) (~cur<%List> _6)) (= (~ret<Int> _5) (~cur<Int> _5)) (= _! true))
  (%main.5 _1 _2 _5 _6 _10 _13 true _!))))

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

; %take_some_rest
(assert (forall ((_1 ~Mut<%List>) (_@ ~Tup<~Mut<Int>-~Mut<%List>>)) (=>
  (and (%take_some_rest.0 _1 _@))
  (%take_some_rest _1 _@))))
; %take_some_rest bb0
(assert (forall ((_1 ~Mut<%List>) (_@ ~Tup<~Mut<Int>-~Mut<%List>>) (_?.3 Bool) (_*.3_1 Int) (_*.3_3 %List) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%take_some_rest.4 (~mut<%List> (%List-0 _*.3_1 _*.3_3) (~ret<%List> _1)) (~mut<Int> _$.0_0/0 _*.3_1) (~mut<%List> _$.0_0/1 _*.3_3) _?.3 _@))
  (%take_some_rest.0 (~mut<%List> (%List-0 _$.0_0/0 _$.0_0/1) (~ret<%List> _1)) _@))))
(assert (forall ((_1 ~Mut<%List>) (_@ ~Tup<~Mut<Int>-~Mut<%List>>) (_@.1 ~Tup<~Mut<Int>-~Mut<%List>>) (_*.1_1 %List)) (=>
  (and (%take_some_rest (~mut<%List> %List-1 _*.1_1) _@.1) (= (~ret<%List> _1) _*.1_1) (= _@ _@.1))
  (%take_some_rest.0 (~mut<%List> %List-1 (~ret<%List> _1)) _@))))
; %take_some_rest bb4
(assert (forall ((_1 ~Mut<%List>) (_3 ~Mut<Int>) (_4 ~Mut<%List>) (_@ ~Tup<~Mut<Int>-~Mut<%List>>) (_@.5 ~Tup<~Mut<Int>-~Mut<%List>>) (_*.5_1 %List)) (=>
  (and (%take_some_rest (~mut<%List> (~cur<%List> _4) _*.5_1) _@.5) (= (~ret<%List> _4) _*.5_1) (= (~ret<Int> _3) (~cur<Int> _3)) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ _@.5))
  (%take_some_rest.4 _1 _3 _4 false _@))))
(assert (forall ((_1 ~Mut<%List>) (_3 ~Mut<Int>) (_4 ~Mut<%List>) (_@ ~Tup<~Mut<Int>-~Mut<%List>>) (_*.6_1 Int) (_*.6_3 %List)) (=>
  (and (= (~ret<%List> _4) _*.6_3) (= (~ret<Int> _3) _*.6_1) (= (~ret<%List> _1) (~cur<%List> _1)) (= _@ (~tup<~Mut<Int>-~Mut<%List>> (~mut<Int> (~cur<Int> _3) _*.6_1) (~mut<%List> (~cur<%List> _4) _*.6_3))))
  (%take_some_rest.4 _1 _3 _4 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
