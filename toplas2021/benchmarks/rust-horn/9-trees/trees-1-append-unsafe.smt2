(set-logic HORN)

(declare-datatypes ((%Tree 0)) ((par () (
  (%Tree-0 (%Tree-0.0 %Tree) (%Tree-0.1 Int) (%Tree-0.2 %Tree))
  %Tree-1))))

(declare-datatypes ((~Mut<%Tree> 0)) ((par () ((~mut<%Tree> (~cur<%Tree> %Tree) (~ret<%Tree> %Tree))))))

(declare-fun %append (~Mut<%Tree> %Tree) Bool)
(declare-fun %append.0 (~Mut<%Tree> %Tree) Bool)
(declare-fun %append.4 (~Mut<%Tree> %Tree ~Mut<%Tree> ~Mut<%Tree> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.6 (%Tree %Tree Int Int Int Bool Bool) Bool)
(declare-fun %sum (%Tree Int) Bool)
(declare-fun %sum.0 (%Tree Int) Bool)

; %append
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree)) (=>
  (and (%append.0 _1 _2))
  (%append _1 _2))))
; %append bb0
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_?.3 Bool) (_*.3_1 %Tree) (_*.3_3 %Tree) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%append.4 (~mut<%Tree> (%Tree-0 _*.3_1 _$.0_0/1 _*.3_3) (~ret<%Tree> _1)) _2 (~mut<%Tree> _$.0_0/0 _*.3_1) (~mut<%Tree> _$.0_0/2 _*.3_3) _?.3))
  (%append.0 (~mut<%Tree> (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) (~ret<%Tree> _1)) _2))))
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree)) (=>
  (and (= (~ret<%Tree> _1) _2) true)
  (%append.0 (~mut<%Tree> %Tree-1 (~ret<%Tree> _1)) _2))))
; %append bb4
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_4 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_*.5_1 %Tree)) (=>
  (and (%append (~mut<%Tree> (~cur<%Tree> _5) _*.5_1) _2) (= (~ret<%Tree> _5) _*.5_1) (= (~ret<%Tree> _4) (~cur<%Tree> _4)) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) true)
  (%append.4 _1 _2 _4 _5 false))))
(assert (forall ((_1 ~Mut<%Tree>) (_2 %Tree) (_4 ~Mut<%Tree>) (_5 ~Mut<%Tree>) (_*.6_1 %Tree)) (=>
  (and (%append (~mut<%Tree> (~cur<%Tree> _4) _*.6_1) _2) (= (~ret<%Tree> _5) (~cur<%Tree> _5)) (= (~ret<%Tree> _4) _*.6_1) (= (~ret<%Tree> _1) (~cur<%Tree> _1)) true)
  (%append.4 _1 _2 _4 _5 true))))

; %main
(assert (forall ((_! Bool) (_@.2 Int) (_@.3 Int) (_@.5 Int) (_?.0 %Tree) (_?.1 %Tree) (_*.4_5 %Tree) (_*.4_6 %Tree) (_%.0 %Tree)) (=>
  (and (%sum _?.0 _@.2) (%sum _?.1 _@.3) (%append (~mut<%Tree> _?.0 _*.4_6) _?.1) (= _*.4_5 _*.4_6) (%sum _*.4_5 _@.5) (%main.6 _*.4_5 _%.0 _@.2 _@.3 _@.5 (not (> _@.5 (+ _@.2 _@.3))) _!))
  (%main _!))))
; %main bb6
(assert (forall ((_1 %Tree) (_2 %Tree) (_3 Int) (_6 Int) (_13 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.6 _1 _2 _3 _6 _13 false _!))))
(assert (forall ((_1 %Tree) (_2 %Tree) (_3 Int) (_6 Int) (_13 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.6 _1 _2 _3 _6 _13 true _!))))

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
