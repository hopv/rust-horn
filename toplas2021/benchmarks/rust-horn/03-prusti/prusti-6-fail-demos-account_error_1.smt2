(set-logic HORN)

(declare-datatypes ((%Account 0)) ((par () (
  (%Account-0 (%Account-0.0 Int))))))

(declare-datatypes ((~Mut<%Account> 0)) ((par () ((~mut<%Account> (~cur<%Account> %Account) (~ret<%Account> %Account))))))

(declare-fun %Account/balance (%Account Int) Bool)
(declare-fun %Account/deposit (~Mut<%Account> Int) Bool)
(declare-fun %Account/withdraw (~Mut<%Account> Int) Bool)
(declare-fun %main (Bool) Bool)
(declare-fun %main.7 (%Account %Account Int Int Bool Bool) Bool)

; %Account/balance
(assert (forall ((_1 %Account) (_@ Int)) (=>
  (and (= _@ (%Account-0.0 _1)))
  (%Account/balance _1 _@))))

; %Account/deposit
(assert (forall ((_1 ~Mut<%Account>) (_2 Int)) (=>
  (and (= (~ret<%Account> _1) (%Account-0 (+ (%Account-0.0 (~cur<%Account> _1)) _2))) true)
  (%Account/deposit _1 _2))))

; %Account/withdraw
(assert (forall ((_1 ~Mut<%Account>) (_2 Int)) (=>
  (and (= (~ret<%Account> _1) (%Account-0 (- (%Account-0.0 (~cur<%Account> _1)) _2))) true)
  (%Account/withdraw _1 _2))))

; %main
(assert (forall ((_! Bool) (_@.3 Int) (_@.6 Int) (_?.0 %Account) (_?.1 %Account) (_?.2 Int) (_*.4_3 %Account) (_*.5_5 %Account)) (=>
  (and (%Account/balance _?.0 _@.3) (%Account/withdraw (~mut<%Account> _?.0 _*.4_3) _?.2) (%Account/deposit (~mut<%Account> _?.1 _*.5_5) _?.2) (%Account/balance _*.4_3 _@.6) (%main.7 _*.4_3 _*.5_5 _?.2 _@.3 (not (= _@.6 (+ _@.3 _?.2))) _!))
  (%main _!))))
; %main bb7
(assert (forall ((_1 %Account) (_2 %Account) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.7 _1 _2 _3 _4 false _!))))
(assert (forall ((_1 %Account) (_2 %Account) (_3 Int) (_4 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.7 _1 _2 _3 _4 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
