(set-logic HORN)

(declare-datatypes ((%Tree 0)) ((par () (
  (%Tree-0 (%Tree-0.0 %Tree) (%Tree-0.1 Int) (%Tree-0.2 %Tree))
  %Tree-1))))

(declare-datatypes ((~Mut<%Tree> 0)) ((par () ((~mut<%Tree> (~cur<%Tree> %Tree) (~ret<%Tree> %Tree))))))
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %append_some (~Mut<%Tree> %Tree) Bool)
(declare-fun %append_some.0 (~Mut<%Tree> %Tree) Bool)
(declare-fun %append_some.5 (~Mut<%Tree> %Tree ~Mut<%Tree> ~Mut<Int> ~Mut<%Tree> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.8 (%Tree %Tree Bool Bool) Bool)
(declare-fun %sum (%Tree Int) Bool)
(declare-fun %sum.0 (%Tree Int) Bool)

; %append_some
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree)) (=>
  (and (%append_some.0 _1 _2))
  (%append_some _1 _2))))
; %append_some bb0
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_?.4 Bool) (_*.4_1 %Tree) (_*.4_3 Int) (_*.4_5 %Tree) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%append_some.5 (~mut<%Tree> (%Tree-0 _*.4_1 _*.4_3 _*.4_5) (~ret<%Tree> _1)) _2 (~mut<%Tree> _$.0_0/0 _*.4_1) (~mut<Int> _$.0_0/1 _*.4_3) (~mut<%Tree> _$.0_0/2 _*.4_5) _?.4))
  (%append_some.0 (~mut<%Tree> (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) (~ret<%Tree> _1)) _2))))
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree)) (=>
  (and (= (~ret<%Tree> _1) _2) true)
  (%append_some.0 (~mut<%Tree> %Tree-1 (~ret<%Tree> _1)) _2))))
; %append_some bb5
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_4 ~Mut<%Tree>) (_5 ~Mut<Int>) (_6 ~Mut<%Tree>) (_*.6_1 %Tree)) (=>
  (and (%append_some (~mut<%Tree> (~cur<%Tree> _6) _*.6_1) _2) (= (~ret<%Tree> _6) _*.6_1) (= (~ret<Int> _5) (~cur<Int> _5)) (= (~ret<%Tree> _4) (~cur<%Tree> _4)) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) true)
  (%append_some.5 _1 _2 _4 _5 _6 false))))
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_4 ~Mut<%Tree>) (_5 ~Mut<Int>) (_6 ~Mut<%Tree>) (_*.7_1 %Tree)) (=>
  (and (%append_some (~mut<%Tree> (~cur<%Tree> _4) _*.7_1) _2) (= (~ret<%Tree> _6) (~cur<%Tree> _6)) (= (~ret<Int> _5) (~cur<Int> _5)) (= (~ret<%Tree> _4) _*.7_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) true)
  (%append_some.5 _1 _2 _4 _5 _6 true))))

; %main
(assert (forall ((_! Bool) (_@.3 Int) (_@.5 Int) (_@.7 Int) (_?.0 %Tree) (_?.2 %Tree) (_*.6_5 %Tree) (_*.6_6 %Tree) (_%.0 %Tree)) (=>
  (and (%sum _?.0 _@.3) (%sum _?.2 _@.5) (%append_some (~mut<%Tree> _?.0 _*.6_6) _?.2) (= _*.6_5 _*.6_6) (%sum _*.6_5 _@.7) (%main.8 _*.6_5 _%.0 (not (> _@.7 (+ _@.3 _@.5))) _!))
  (%main _!))))
; %main bb8
(assert (forall ((_1 %Tree) (_2 %Tree) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 false _!))))
(assert (forall ((_1 %Tree) (_2 %Tree) (_! Bool)) (=>
  (and (= _! true))
  (%main.8 _1 _2 true _!))))

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

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
