(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))

(declare-fun %inc (~Mut<%List>) Bool)
(declare-fun %inc.0 (~Mut<%List>) Bool)
(declare-fun %length (%List Int) Bool)
(declare-fun %length.0 (%List Int) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.7 (%List Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)

; %inc
(assert (forall ((_1 ~Mut<%List>)) (=>
  (and (%inc.0 _1))
  (%inc _1))))
; %inc bb0
(assert (forall ((_1 ~Mut<%List>) (_*.2_1 Int) (_*.2_3 %List) (_*.2_7 %List) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%inc (~mut<%List> _$.0_0/1 _*.2_7)) (= _*.2_3 _*.2_7) (= _*.2_1 (+ _$.0_0/0 1)) (= (~ret<%List> _1) (%List-0 _*.2_1 _*.2_3)) true)
  (%inc.0 (~mut<%List> (%List-0 _$.0_0/0 _$.0_0/1) (~ret<%List> _1))))))
(assert (forall ((_1 ~Mut<%List>)) (=>
  (and (= (~ret<%List> _1) %List-1) true)
  (%inc.0 (~mut<%List> %List-1 (~ret<%List> _1))))))

; %length
(assert (forall ((_1 %List) (_@ Int)) (=>
  (and (%length.0 _1 _@))
  (%length _1 _@))))
; %length bb0
(assert (forall ((_@ Int) (_@.3 Int) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%length _$.0_0/1 _@.3) (= _@ (+ 1 _@.3)))
  (%length.0 (%List-0 _$.0_0/0 _$.0_0/1) _@))))
(assert (forall ((_@ Int)) (=>
  (and (= _@ 0))
  (%length.0 %List-1 _@))))

; %main
(assert (forall ((_! Bool) (_@.2 Int) (_@.3 Int) (_@.6 Int) (_?.0 %List) (_*.5_5 %List) (_*.5_6 %List)) (=>
  (and (%sum _?.0 _@.2) (%length _?.0 _@.3) (%inc (~mut<%List> _?.0 _*.5_6)) (= _*.5_5 _*.5_6) (%sum _*.5_5 _@.6) (%main.7 _*.5_5 (not (> _@.6 (+ _@.2 _@.3))) _!))
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

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
