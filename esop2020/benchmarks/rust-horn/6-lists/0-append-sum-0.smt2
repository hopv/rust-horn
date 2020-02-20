(set-logic HORN)

(declare-datatypes ((%List 0)) ((par () (
  (%List-0 (%List-0.0 Int) (%List-0.1 %List))
  %List-1))))

(declare-datatypes ((~Mut<%List> 0)) ((par () ((~mut<%List> (~cur<%List> %List) (~ret<%List> %List))))))

(declare-fun %append (~Mut<%List> %List) Bool)
(declare-fun %append.0 (~Mut<%List> %List) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.8 (%List %List Bool Bool) Bool)
(declare-fun %sum (%List Int) Bool)
(declare-fun %sum.0 (%List Int) Bool)

; %append
(assert (forall ((_1 ~Mut<%List>) (_2 %List)) (=>
  (and (%append.0 _1 _2))
  (%append _1 _2))))
; %append bb0
(assert (forall ((_1 ~Mut<%List>) (_2 %List) (_*.3_1 %List) (_*.3_3 %List) (_$.0_0/0 Int) (_$.0_0/1 %List)) (=>
  (and (%append (~mut<%List> _$.0_0/1 _*.3_3) _2) (= _*.3_1 _*.3_3) (= (~ret<%List> _1) (%List-0 _$.0_0/0 _*.3_1)) true)
  (%append.0 (~mut<%List> (%List-0 _$.0_0/0 _$.0_0/1) (~ret<%List> _1)) _2))))
(assert (forall ((_1 ~Mut<%List>) (_2 %List)) (=>
  (and (= (~ret<%List> _1) _2) true)
  (%append.0 (~mut<%List> %List-1 (~ret<%List> _1)) _2))))

; %main
(assert (forall ((_! Bool) (_@.3 Int) (_@.5 Int) (_@.7 Int) (_?.0 %List) (_?.2 %List) (_*.6_5 %List) (_*.6_6 %List) (_%.0 %List)) (=>
  (and (%sum _?.0 _@.3) (%sum _?.2 _@.5) (%append (~mut<%List> _?.0 _*.6_6) _?.2) (= _*.6_5 _*.6_6) (%sum _*.6_5 _@.7) (%main.8 _*.6_5 _%.0 (not (= _@.7 (+ _@.3 _@.5))) _!))
  (%main _!))))
; %main bb8
(assert (forall ((_1 %List) (_2 %List) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 false _!))))
(assert (forall ((_1 %List) (_2 %List) (_! Bool)) (=>
  (and (= _! true))
  (%main.8 _1 _2 true _!))))

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
