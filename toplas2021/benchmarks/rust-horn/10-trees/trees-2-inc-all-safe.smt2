(set-logic HORN)

(declare-datatypes ((%Tree 0)) ((par () (
  (%Tree-0 (%Tree-0.0 %Tree) (%Tree-0.1 Int) (%Tree-0.2 %Tree))
  %Tree-1))))
(declare-datatypes ((%std/alloc/Global 0)) ((par () (
  %std/alloc/Global-0))))

(declare-datatypes ((~Mut<%Tree> 0)) ((par () ((~mut<%Tree> (~cur<%Tree> %Tree) (~ret<%Tree> %Tree))))))

(declare-fun %inc (~Mut<%Tree>) Bool)
(declare-fun %inc.0 (~Mut<%Tree>) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.5 (%Tree Int Int Int Bool Bool) Bool)
(declare-fun %size (%Tree Int) Bool)
(declare-fun %size.0 (%Tree Int) Bool)
(declare-fun %sum (%Tree Int) Bool)
(declare-fun %sum.0 (%Tree Int) Bool)

; %inc
(assert (forall ((_1 ~Mut<%Tree>)) (=>
  (and (%inc.0 _1))
  (%inc _1))))
; %inc bb0
(assert (forall ((_1 ~Mut<%Tree>) (_*.3_1 %Tree) (_*.3_3 Int) (_*.3_5 %Tree) (_*.3_8 %Tree) (_*.4_5 %Tree) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%inc (~mut<%Tree> _$.0_0/0 _*.3_8)) (%inc (~mut<%Tree> _$.0_0/2 _*.4_5)) (= _*.3_5 _*.4_5) (= _*.3_3 (+ _$.0_0/1 1)) (= _*.3_1 _*.3_8) (= (~ret<%Tree> _1) (%Tree-0 _*.3_1 _*.3_3 _*.3_5)) true)
  (%inc.0 (~mut<%Tree> (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) (~ret<%Tree> _1))))))
(assert (forall ((_1 ~Mut<%Tree>)) (=>
  (and (= (~ret<%Tree> _1) %Tree-1) true)
  (%inc.0 (~mut<%Tree> %Tree-1 (~ret<%Tree> _1))))))

; %main
(assert (forall ((_! Bool) (_@.1 Int) (_@.2 Int) (_@.4 Int) (_?.0 %Tree) (_*.3_5 %Tree) (_*.3_6 %Tree)) (=>
  (and (%sum _?.0 _@.1) (%size _?.0 _@.2) (%inc (~mut<%Tree> _?.0 _*.3_6)) (= _*.3_5 _*.3_6) (%sum _*.3_5 _@.4) (%main.5 _*.3_5 _@.1 _@.2 _@.4 (not (= _@.4 (+ _@.1 _@.2))) _!))
  (%main _!))))
; %main bb5
(assert (forall ((_1 %Tree) (_2 Int) (_5 Int) (_11 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.5 _1 _2 _5 _11 false _!))))
(assert (forall ((_1 %Tree) (_2 Int) (_5 Int) (_11 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.5 _1 _2 _5 _11 true _!))))

; %size
(assert (forall ((_1 %Tree) (_@ Int)) (=>
  (and (%size.0 _1 _@))
  (%size _1 _@))))
; %size bb0
(assert (forall ((_@ Int) (_@.3 Int) (_@.4 Int) (_$.0_0/0 %Tree) (_$.0_0/1 Int) (_$.0_0/2 %Tree)) (=>
  (and (%size _$.0_0/0 _@.3) (%size _$.0_0/2 _@.4) (= _@ (+ (+ _@.3 1) _@.4)))
  (%size.0 (%Tree-0 _$.0_0/0 _$.0_0/1 _$.0_0/2) _@))))
(assert (forall ((_@ Int)) (=>
  (and (= _@ 0))
  (%size.0 %Tree-1 _@))))

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
