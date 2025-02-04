(set-logic HORN)

; library definitions
(declare-datatypes ((ChannelBuf<Int> 0)) ((par () ((insert (head Int) (tail ChannelBuf<Int>)) (nilBuf)))))

; adt definitions
(declare-datatypes ((%Receiver 0)) ((par () (
  %Receiver-0))))
(declare-datatypes ((%Sender 0)) ((par () (
  %Sender-0))))

; library definitions
(declare-fun MergeInt (ChannelBuf<Int> ChannelBuf<Int> ChannelBuf<Int>) Bool)
(assert (MergeInt nilBuf nilBuf nilBuf))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt (insert n x1) x2 (insert n x)))))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt x1 (insert n x2) (insert n x)))))

; functions
(declare-fun %main (Bool) Bool)
(declare-fun %main.8 (ChannelBuf<Int> ChannelBuf<Int> ChannelBuf<Int> Int Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_@0.0 ChannelBuf<Int>) (_*.1_8 ChannelBuf<Int>) (_*.2_4 ChannelBuf<Int>) (_@0.2 ChannelBuf<Int>) (_*.3_4 ChannelBuf<Int>) (_@0.6 Int) (_*.6_4 ChannelBuf<Int>) (_@0.7 Int) (_*.7_4 ChannelBuf<Int>) (_%.nonce ChannelBuf<Int>)) (=>
  (and (= _@0.0 (insert 1 _*.1_8)) (MergeInt _*.2_4 _@0.2 _*.1_8) (= _@0.2 (insert 2 _*.3_4)) (= _*.2_4 nilBuf) (= _*.3_4 nilBuf) (= _@0.0 (insert _@0.6 _*.6_4)) (= _*.6_4 (insert _@0.7 _*.7_4)) (%main.8 _%.nonce _*.7_4 _%.nonce _@0.6 _@0.7 (= (+ _@0.6 _@0.7) 3) _!))
  (%main _!))))
; %main bb8
(assert (forall ((_1 ChannelBuf<Int>) (_2 ChannelBuf<Int>) (_6 ChannelBuf<Int>) (_14 Int) (_16 Int) (_! Bool)) (=>
  (and (= _! true))
  (%main.8 _1 _2 _6 _14 _16 false _!))))
(assert (forall ((_1 ChannelBuf<Int>) (_2 ChannelBuf<Int>) (_6 ChannelBuf<Int>) (_14 Int) (_16 Int) (_! Bool)) (=>
  (and (= _! false))
  (%main.8 _1 _2 _6 _14 _16 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
