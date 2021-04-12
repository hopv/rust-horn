(set-logic HORN)

(declare-datatypes ((%Point 0)) ((par () (
  (%Point-0 (%Point-0.0 Int) (%Point-0.1 Int))))))
(declare-datatypes ((%std/alloc/Global 0)) ((par () (
  %std/alloc/Global-0))))

(declare-datatypes ((~Mut<%Point> 0)) ((par () ((~mut<%Point> (~cur<%Point> %Point) (~ret<%Point> %Point))))))

(declare-datatypes ((~Tup<%Point-%Point> 0)) ((par () ((~tup<%Point-%Point> (~at0/<%Point-%Point> %Point) (~at1/<%Point-%Point> %Point))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.2 (~Tup<%Point-%Point> ~Mut<%Point> ~Mut<%Point> Int Bool Bool) Bool)
(declare-fun %shift_x (~Mut<%Point> Int) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 ~Tup<%Point-%Point>) (_*.1_1 %Point) (_*.1_3 %Point) (_*.1_8 %Point)) (=>
  (and (%shift_x (~mut<%Point> (~at1/<%Point-%Point> _?.0) _*.1_8) (- (%Point-0.0 (~at0/<%Point-%Point> _?.0)) (%Point-0.0 (~at1/<%Point-%Point> _?.0)))) (%main.2 (~tup<%Point-%Point> (~at0/<%Point-%Point> _?.0) _*.1_1) (~mut<%Point> _*.1_3 _*.1_1) (~mut<%Point> _*.1_8 _*.1_3) (%Point-0.0 (~at1/<%Point-%Point> _?.0)) (not (= (%Point-0.0 (~at0/<%Point-%Point> _?.0)) (%Point-0.0 _*.1_1))) _!))
  (%main _!))))
; %main bb2
(assert (forall ((_1 ~Tup<%Point-%Point>) (_2 ~Mut<%Point>) (_3 ~Mut<%Point>) (_4 Int) (_! Bool)) (=>
  (and (= (~ret<%Point> _3) (~cur<%Point> _3)) (= (~ret<%Point> _2) (~cur<%Point> _2)) (= _! false))
  (%main.2 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 ~Tup<%Point-%Point>) (_2 ~Mut<%Point>) (_3 ~Mut<%Point>) (_4 Int) (_! Bool)) (=>
  (and (= (~ret<%Point> _2) (~cur<%Point> _2)) (= (~ret<%Point> _3) (~cur<%Point> _3)) (= _! true))
  (%main.2 _1 _2 _3 _4 true _!))))

; %shift_x
(assert (forall ((_1 ~Mut<%Point>) (_2 Int)) (=>
  (and (= (~ret<%Point> _1) (%Point-0 (+ (%Point-0.0 (~cur<%Point> _1)) _2) (%Point-0.1 (~cur<%Point> _1)))) true)
  (%shift_x _1 _2))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
