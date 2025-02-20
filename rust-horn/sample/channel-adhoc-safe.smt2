(set-logic HORN)

; library definitions
(declare-datatypes ((ChannelBuf<Int> 0)) ((par () ((insert (content Int) (time Real) (tail ChannelBuf<Int>)) (nilBuf)))))

; adt definitions
(declare-datatypes ((%Receiver 0)) ((par () (
  %Receiver-0))))
(declare-datatypes ((%Sender 0)) ((par () (
  %Sender-0))))

; library definitions
(declare-fun MergeInt (ChannelBuf<Int> ChannelBuf<Int> ChannelBuf<Int>) Bool)
(assert (MergeInt nilBuf nilBuf nilBuf))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int) (t Real))
  (=> (MergeInt x1 x2 x) (MergeInt (insert n t x1) x2 (insert n t x)))))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int) (t Real))
  (=> (MergeInt x1 x2 x) (MergeInt x1 (insert n t x2) (insert n t x)))))
(declare-fun Sorted (ChannelBuf<Int>) Bool)
(assert (Sorted nilBuf))
(assert (forall ((n Int) (t Real))
  (Sorted (insert n t nilBuf))))
(assert (forall ((x ChannelBuf<Int>) (n1 Int) (t1 Real) (n2 Int) (t2 Real))
  (=> (and (<= t1 t2) (Sorted (insert n1 t1 x))) (Sorted (insert n1 t1 (insert n2 t2 x))))))

; functions
(declare-fun %main (Bool) Bool)
(declare-fun %main.8 (ChannelBuf<Int> ChannelBuf<Int> ChannelBuf<Int> Int Int Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_@0.0 ChannelBuf<Int>) (_@0 Real) (_*.1_8 ChannelBuf<Int>) (_*.2_4 ChannelBuf<Int>) (_@0.2 ChannelBuf<Int>) (_*.3_4 ChannelBuf<Int>) (_@0.6 Int) (_@1 Real) (_*.6_4 ChannelBuf<Int>) (_@2 Real) (_@0.7 Int) (_@3 Real) (_*.7_4 ChannelBuf<Int>) (_@4 Real) (_%.nonce ChannelBuf<Int>)) (=>
  (and (Sorted _@0.0) (= _@0.0 (insert 1 _@0 _*.1_8)) (MergeInt _*.2_4 _@0.2 _*.1_8) (= _@0.2 (insert 2 _@0 _*.3_4)) (= _*.2_4 nilBuf) (= _*.3_4 nilBuf) (= _@0.0 (insert _@0.6 _@1 _*.6_4)) (< _@1 _@2) (<= _@0 _@2) (= _*.6_4 (insert _@0.7 _@3 _*.7_4)) (< _@3 _@4) (<= _@2 _@4) (%main.8 _%.nonce _*.7_4 _%.nonce _@0.6 _@0.7 (= (+ _@0.6 _@0.7) 3) _!))
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
