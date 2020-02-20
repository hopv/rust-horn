(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-datatypes ((~Tup<~Mut<Int>-~Mut<%List>> 0)) ((par () ((~tup<~Mut<Int>-~Mut<%List>> (~at0/<~Mut<Int>-~Mut<%List>> ~Mut<Int>) (~at1/<~Mut<Int>-~Mut<%List>> ~Mut<%List>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.7 (%List Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)
(declare-fun %take_some_rest (~Mut<%List> ~Tup<~Mut<Int>-~Mut<%List>>) Bool)
(declare-fun %take_some_rest.0 (~Mut<%List> ~Tup<~Mut<Int>-~Mut<%List>>) Bool)
(declare-fun %take_some_rest.4 (~Mut<%List> ~Mut<Int> ~Mut<%List> Bool ~Tup<~Mut<Int>-~Mut<%List>>) Bool)

; %main
(assert (forall ((_! Bool) (_@.2 Int) (_@.3 ~Tup<~Mut<Int>-~Mut<%List>>) (_@.5 ~Tup<~Mut<Int>-~Mut<%List>>) (_@.6 Int) (_?.0 %List) (_*.3_5 %List) (_*.3_6 %List) (_*.5_9 %List)) (=>
  (and (%sum _?.0 _@.2) (%take_some_rest (~mut<%List> _?.0 _*.3_6) _@.3) (= _*.3_5 _*.3_6) (%take_some_rest (~mut<%List> (~cur<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.3)) _*.5_9) _@.5) (= (~ret<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.5)) (~cur<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.5))) (%sum _*.3_5 _@.6) (= (~ret<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.3)) (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.3)) 1)) (= (~ret<%List> (~at1/<~Mut<Int>-~Mut<%List>> _@.3)) _*.5_9) (= (~ret<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.5)) (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%List>> _@.5)) 1)) (%main.7 _*.3_5 (not (= _@.6 (+ _@.2 2))) _!))
  (%main _!))))
; %main bb7
(assert (forall ((_1 %List) (_! Bool)) (=>
  (and (= _! false))
  (%main.7 _1 false _!))))
(assert (forall ((_1 %List) (_! Bool)) (=>
  (and (= _! true))
  (%main.7 _1 true _!))))

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
