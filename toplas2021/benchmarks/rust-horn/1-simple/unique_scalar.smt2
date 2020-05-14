(set-logic HORN)

(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

(declare-fun %main (Bool) Bool)
(declare-fun %main.1 (Int Int Bool Bool) Bool)
(declare-fun %main.4 (Int Int ~Mut<Int> Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Bool)) (=>
  (and (%main.1 0 0 _?.0 _!))
  (%main _!))))
; %main bb1
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_*.2_1 Int) (_*.2_2 Int)) (=>
  (and (= _*.2_1 _*.2_2) (%main.4 (+ _1 1) _*.2_1 (~mut<Int> 1 _*.2_2) (not (< (+ _1 1) 2)) _!))
  (%main.1 _1 _2 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_! Bool) (_*.3_0 Int)) (=>
  (and (%main.4 (+ _*.3_0 1) _2 (~mut<Int> 1 _*.3_0) (not (< (+ _*.3_0 1) 2)) _!))
  (%main.1 _1 _2 true _!))))
; %main bb4
(assert (forall ((_1 Int) (_2 Int) (_3 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= _! false))
  (%main.4 _1 _2 _3 false _!))))
(assert (forall ((_1 Int) (_2 Int) (_3 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _3) (~cur<Int> _3)) (= _! true))
  (%main.4 _1 _2 _3 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
