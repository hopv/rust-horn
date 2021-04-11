(set-logic HORN)

(declare-datatypes ((%Tree 0)) ((par () (
  (%Tree-0 (%Tree-0.0 %Tree) (%Tree-0.1 Int) (%Tree-0.2 %Tree))
  %Tree-1))))
(declare-datatypes ((%std/alloc/Global 0)) ((par () (
  %std/alloc/Global-0))))

(declare-datatypes ((~Mut<%Tree> 0)) ((par () ((~mut<%Tree> (~cur<%Tree> %Tree) (~ret<%Tree> %Tree))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-datatypes ((~Tup<~Mut<Int>-~Mut<%Tree>> 0)) ((par () ((~tup<~Mut<Int>-~Mut<%Tree>> (~at0/<~Mut<Int>-~Mut<%Tree>> ~Mut<Int>) (~at1/<~Mut<Int>-~Mut<%Tree>> ~Mut<%Tree>))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (%Tree Int ~Mut<Int> ~Mut<%Tree> ~Mut<Int> Int Bool Bool) Bool)
(declare-fun %sum (%Tree Int) Bool)
(declare-fun %sum.0 (%Tree Int) Bool)
(declare-fun %take_some_rest (~Mut<%Tree> ~Tup<~Mut<Int>-~Mut<%Tree>>) Bool)
(declare-fun %take_some_rest.0 (~Mut<%Tree> ~Tup<~Mut<Int>-~Mut<%Tree>>) Bool)
(declare-fun %take_some_rest.4 (~Mut<%Tree> ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool ~Tup<~Mut<Int>-~Mut<%Tree>>) Bool)
(declare-fun %take_some_rest.7 (~Mut<%Tree> ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool ~Mut<Int> Bool ~Tup<~Mut<Int>-~Mut<%Tree>>) Bool)
(declare-fun %take_some_rest.11 (~Mut<%Tree> ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool Bool ~Tup<~Mut<Int>-~Mut<%Tree>>) Bool)

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_@.2 ~Tup<~Mut<Int>-~Mut<%Tree>>) (_@.3 ~Tup<~Mut<Int>-~Mut<%Tree>>) (_@.4 Int) (_?.0 %Tree) (_*.2_5 %Tree) (_*.2_6 %Tree) (_*.3_9 %Tree)) (=>
  (and (%sum _?.0 _@.1) (%take_some_rest (~mut<%Tree> _?.0 _*.2_6) _@.2) (= _*.2_5 _*.2_6) (%take_some_rest (~mut<%Tree> (~cur<%Tree> (~at1/<~Mut<Int>-~Mut<%Tree>> _@.2)) _*.3_9) _@.3) (= (~ret<%Tree> (~at1/<~Mut<Int>-~Mut<%Tree>> _@.3)) (~cur<%Tree> (~at1/<~Mut<Int>-~Mut<%Tree>> _@.3))) (%sum _*.2_5 _@.4) (%main.5 _*.2_5 _@.1 (~mut<Int> (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%Tree>> _@.2)) 1) (~ret<Int> (~at0/<~Mut<Int>-~Mut<%Tree>> _@.2))) (~mut<%Tree> _*.3_9 (~ret<%Tree> (~at1/<~Mut<Int>-~Mut<%Tree>> _@.2))) (~mut<Int> (+ (~cur<Int> (~at0/<~Mut<Int>-~Mut<%Tree>> _@.3)) 1) (~ret<Int> (~at0/<~Mut<Int>-~Mut<%Tree>> _@.3))) _@.4 (not (> _@.4 (+ _@.1 2))) _!))
  (%main _!))))
; %main bb5
(assert (forall ((_1 %Tree) (_2 Int) (_5 ~Mut<Int>) (_6 ~Mut<%Tree>) (_10 ~Mut<Int>) (_13 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _10) (~cur<Int> _10)) (= (~ret<%Tree> _6) (~cur<%Tree> _6)) (= (~ret<Int> _5) (~cur<Int> _5)) (= _! false))
  (%main.5 _1 _2 _5 _6 _10 _13 false _!))))
(assert (forall ((_1 %Tree) (_2 Int) (_5 ~Mut<Int>) (_6 ~Mut<%Tree>) (_10 ~Mut<Int>) (_13 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _5) (~cur<Int> _5)) (= (~ret<%Tree> _6) (~cur<%Tree> _6)) (= (~ret<Int> _10) (~cur<Int> _10)) (= _! true))
  (%main.5 _1 _2 _5 _6 _10 _13 true _!))))

; %sum
(assert (forall ((_1 %Tree) (_@ Int)) (=>
  (and (%sum.0 _1 _@))
  (%sum _1 _@))))
; %sum bb0
(assert (forall ((_@ Int) (_@.3 Int) (_@.5 Int) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%sum _$.0_0/0 _@.3) (%sum _$.0_0/2 _@.5) (= _@ (+ (+ _@.3 _$.0_0/1) _@.5)))
  (%sum.0 (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) _@))))
(assert (forall ((_@ Int)) (=>
  (and (= _@ 0))
  (%sum.0 %Tree-1 _@))))

; %take_some_rest
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>)) (=>
  (and (%take_some_rest.0 _1 _@))
  (%take_some_rest _1 _@))))
; %take_some_rest bb0
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_?.3 Bool) (_*.3_1 %Tree) (_*.3_3 Int) (_*.3_5 %Tree) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%take_some_rest.4 (~mut<%Tree> (%Tree-0 _*.3_1 _*.3_3 _*.3_5) (~ret<%Tree> _1)) (~mut<%Tree> _$.0_0/0 _*.3_1) (~mut<Int> _$.0_0/1 _*.3_3) (~mut<%Tree> _$.0_0/2 _*.3_5) _?.3 _@))
  (%take_some_rest.0 (~mut<%Tree> (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) (~ret<%Tree> _1)) _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_@.1 ~Tup<~Mut<Int>-~Mut<%Tree>>) (_*.1_1 %Tree)) (=>
  (and (%take_some_rest (~mut<%Tree> %Tree-1 _*.1_1) _@.1) (= (~ret<%Tree> _1) _*.1_1) (= _@ _@.1))
  (%take_some_rest.0 (~mut<%Tree> %Tree-1 (~ret<%Tree> _1)) _@))))
; %take_some_rest bb4
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_?.6 Bool)) (=>
  (and (%take_some_rest.11 _1 _3 _4 _5 false _?.6 _@))
  (%take_some_rest.4 _1 _3 _4 _5 false _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_?.5 Bool) (_*.5_1 Int)) (=>
  (and (%take_some_rest.7 _1 _3 (~mut<Int> _*.5_1 (~ret<Int> _4)) _5 true (~mut<Int> (~cur<Int> _4) _*.5_1) _?.5 _@))
  (%take_some_rest.4 _1 _3 _4 _5 true _@))))
; %take_some_rest bb7
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_6 Bool) (_7 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_*.9_1 %Tree) (_*.9_2 %Tree) (_*.10_0 %Tree)) (=>
  (and (= _*.9_1 _*.9_2) (= _*.9_2 _*.10_0) (= (~ret<%Tree> _5) _*.9_1) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<%Tree> _3) (~cur<%Tree> _3)) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ (~tup<~Mut<Int>-~Mut<%Tree>> _7 (~mut<%Tree> (~cur<%Tree> _5) _*.10_0))))
  (%take_some_rest.7 _1 _3 _4 _5 _6 _7 false _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_6 Bool) (_7 ~Mut<Int>) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_*.8_1 %Tree) (_*.8_2 %Tree) (_*.10_0 %Tree)) (=>
  (and (= _*.8_1 _*.8_2) (= _*.8_2 _*.10_0) (= (~ret<%Tree> _5) (~cur<%Tree> _5)) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<%Tree> _3) _*.8_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ (~tup<~Mut<Int>-~Mut<%Tree>> _7 (~mut<%Tree> (~cur<%Tree> _3) _*.10_0))))
  (%take_some_rest.7 _1 _3 _4 _5 _6 _7 true _@))))
; %take_some_rest bb11
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_6 Bool) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_@.13 ~Tup<~Mut<Int>-~Mut<%Tree>>) (_*.13_1 %Tree)) (=>
  (and (%take_some_rest (~mut<%Tree> (~cur<%Tree> _5) _*.13_1) _@.13) (= (~ret<%Tree> _5) _*.13_1) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<%Tree> _3) (~cur<%Tree> _3)) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ _@.13))
  (%take_some_rest.11 _1 _3 _4 _5 _6 false _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_3 ~Mut<%Tree>) (_4 ~Mut<Int>) (_5 ~Mut<%Tree>) (_6 Bool) (_@ ~Tup<~Mut<Int>-~Mut<%Tree>>) (_@.12 ~Tup<~Mut<Int>-~Mut<%Tree>>) (_*.12_1 %Tree)) (=>
  (and (%take_some_rest (~mut<%Tree> (~cur<%Tree> _3) _*.12_1) _@.12) (= (~ret<%Tree> _5) (~cur<%Tree> _5)) (= (~ret<Int> _4) (~cur<Int> _4)) (= (~ret<%Tree> _3) _*.12_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ _@.12))
  (%take_some_rest.11 _1 _3 _4 _5 _6 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
