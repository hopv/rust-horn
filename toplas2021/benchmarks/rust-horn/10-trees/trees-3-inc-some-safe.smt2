(set-logic HORN)

(declare-datatypes ((%Tree 0)) ((par () (
  (%Tree-0 (%Tree-0.0 %Tree) (%Tree-0.1 Int) (%Tree-0.2 %Tree))
  %Tree-1))))
(declare-datatypes ((%std/alloc/Global 0)) ((par () (
  %std/alloc/Global-0))))

(declare-datatypes ((~Mut<%Tree> 0)) ((par () ((~mut<%Tree> (~cur<%Tree> %Tree) (~ret<%Tree> %Tree))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.4 (%Tree Int ~Mut<Int> Int Bool Bool) Bool)
(declare-fun %sum (%Tree Int) Bool)
(declare-fun %sum.0 (%Tree Int) Bool)
(declare-fun %take_some (~Mut<%Tree> ~Mut<Int>) Bool)
(declare-fun %take_some.0 (~Mut<%Tree> ~Mut<Int>) Bool)
(declare-fun %take_some.4 (~Mut<%Tree> ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool ~Mut<Int>) Bool)
(declare-fun %take_some.7 (~Mut<%Tree> ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool Bool ~Mut<Int>) Bool)

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_@.2 ~Mut<Int>) (_@.3 Int) (_?.0 %Tree) (_*.2_5 %Tree) (_*.2_6 %Tree)) (=>
  (and (%sum _?.0 _@.1) (%take_some (~mut<%Tree> _?.0 _*.2_6) _@.2) (= _*.2_5 _*.2_6) (%sum _*.2_5 _@.3) (%main.4 _*.2_5 _@.1 (~mut<Int> (+ (~cur<Int> _@.2) 1) (~ret<Int> _@.2)) _@.3 (not (= _@.3 (+ _@.1 1))) _!))
  (%main _!))))
; %main bb4
(assert (forall ((_1 %Tree) (_2 Int) (_5 ~Mut<Int>) (_8 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _5) (~cur<Int> _5)) (= _! false))
  (%main.4 _1 _2 _5 _8 false _!))))
(assert (forall ((_1 %Tree) (_2 Int) (_5 ~Mut<Int>) (_8 Int) (_! Bool)) (=>
  (and (= (~ret<Int> _5) (~cur<Int> _5)) (= _! true))
  (%main.4 _1 _2 _5 _8 true _!))))

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

; %take_some
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Mut<Int>)) (=>
  (and (%take_some.0 _1 _@))
  (%take_some _1 _@))))
; %take_some bb0
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Mut<Int>) (_?.3 Bool) (_*.3_1 %Tree) (_*.3_3 Int) (_*.3_5 %Tree) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%take_some.4 (~mut<%Tree> (%Tree-0 _*.3_1 _*.3_3 _*.3_5) (~ret<%Tree> _1)) (~mut<%Tree> _$.0_0/0 _*.3_1) (~mut<Int> _$.0_0/1 _*.3_3) (~mut<%Tree> _$.0_0/2 _*.3_5) _?.3 _@))
  (%take_some.0 (~mut<%Tree> (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) (~ret<%Tree> _1)) _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_@ ~Mut<Int>) (_@.1 ~Mut<Int>) (_*.1_2 %Tree) (_*.14_0 Int) (_*.15_0 Int) (_*.15_1 Int)) (=>
  (and (%take_some (~mut<%Tree> %Tree-1 _*.1_2) _@.1) (= (~ret<Int> _@.1) _*.14_0) (= _*.14_0 _*.15_0) (= _*.15_0 _*.15_1) (= (~ret<%Tree> _1) _*.1_2) (= _@ (~mut<Int> (~cur<Int> _@.1) _*.15_1)))
  (%take_some.0 (~mut<%Tree> %Tree-1 (~ret<%Tree> _1)) _@))))
; %take_some bb4
(assert (forall ((_1 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_6 ~Mut<Int>) (_7 ~Mut<%Tree>) (_@ ~Mut<Int>) (_?.6 Bool)) (=>
  (and (%take_some.7 _1 _5 _6 _7 false _?.6 _@))
  (%take_some.4 _1 _5 _6 _7 false _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_6 ~Mut<Int>) (_7 ~Mut<%Tree>) (_@ ~Mut<Int>) (_*.5_1 Int) (_*.5_2 Int) (_*.13_0 Int) (_*.13_2 Int) (_*.15_0 Int) (_*.15_1 Int)) (=>
  (and (= _*.5_1 _*.5_2) (= _*.5_2 _*.13_0) (= _*.13_0 _*.13_2) (= (~ret<%Tree> _7) (~cur<%Tree> _7)) (= (~ret<Int> _6) _*.5_1) (= (~ret<%Tree> _5) (~cur<%Tree> _5)) (= _*.13_2 _*.15_0) (= _*.15_0 _*.15_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ (~mut<Int> (~cur<Int> _6) _*.15_1)))
  (%take_some.4 _1 _5 _6 _7 true _@))))
; %take_some bb7
(assert (forall ((_1 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_6 ~Mut<Int>) (_7 ~Mut<%Tree>) (_10 Bool) (_@ ~Mut<Int>) (_@.9 ~Mut<Int>) (_*.9_3 %Tree) (_*.11_0 Int) (_*.11_2 Int) (_*.12_0 Int) (_*.13_0 Int) (_*.13_2 Int) (_*.15_0 Int) (_*.15_1 Int)) (=>
  (and (%take_some (~mut<%Tree> (~cur<%Tree> _7) _*.9_3) _@.9) (= (~ret<Int> _@.9) _*.11_0) (= _*.11_0 _*.11_2) (= _*.11_2 _*.12_0) (= _*.12_0 _*.13_0) (= _*.13_0 _*.13_2) (= (~ret<%Tree> _7) _*.9_3) (= (~ret<Int> _6) (~cur<Int> _6)) (= (~ret<%Tree> _5) (~cur<%Tree> _5)) (= _*.13_2 _*.15_0) (= _*.15_0 _*.15_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ (~mut<Int> (~cur<Int> _@.9) _*.15_1)))
  (%take_some.7 _1 _5 _6 _7 _10 false _@))))
(assert (forall ((_1 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_6 ~Mut<Int>) (_7 ~Mut<%Tree>) (_10 Bool) (_@ ~Mut<Int>) (_@.8 ~Mut<Int>) (_*.8_3 %Tree) (_*.10_0 Int) (_*.10_2 Int) (_*.12_0 Int) (_*.13_0 Int) (_*.13_2 Int) (_*.15_0 Int) (_*.15_1 Int)) (=>
  (and (%take_some (~mut<%Tree> (~cur<%Tree> _5) _*.8_3) _@.8) (= (~ret<Int> _@.8) _*.10_0) (= _*.10_0 _*.10_2) (= _*.10_2 _*.12_0) (= _*.12_0 _*.13_0) (= _*.13_0 _*.13_2) (= (~ret<%Tree> _7) (~cur<%Tree> _7)) (= (~ret<Int> _6) (~cur<Int> _6)) (= (~ret<%Tree> _5) _*.8_3) (= _*.13_2 _*.15_0) (= _*.15_0 _*.15_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) (= _@ (~mut<Int> (~cur<Int> _@.8) _*.15_1)))
  (%take_some.7 _1 _5 _6 _7 _10 true _@))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
