(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %just_rec (~Mut<Int>) Bool)
(declare-fun %just_rec.1 (~Mut<Int> Bool) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (Int Int Bool Bool) Bool)

; %just_rec
(assert (forall ((_1 ~Mut<Int>) (_?.0 Bool)) (=>
  (and (%just_rec.1 _1 _?.0))
  (%just_rec _1))))
; %just_rec bb1
(assert (forall ((_1 ~Mut<Int>) (_?.3 Int) (_*.4_3 Int) (_*.4_4 Int)) (=>
  (and (%just_rec (~mut<Int> _?.3 _*.4_4)) (= _*.4_3 _*.4_4) (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%just_rec.1 _1 false))))
(assert (forall ((_1 ~Mut<Int>)) (=>
  (and (= (~ret<Int> _1) (~cur<Int> _1)) true)
  (%just_rec.1 _1 true))))

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_*.1_5 Int) (_*.1_6 Int)) (=>
  (and (%just_rec (~mut<Int> _?.0 _*.1_6)) (= _*.1_5 _*.1_6) (%main.2 _*.1_5 _?.0 (not (> _?.0 _*.1_5)) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.2 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.2 _1 _2 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
