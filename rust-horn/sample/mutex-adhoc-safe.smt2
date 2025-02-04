(set-logic HORN)

; library definitions
(declare-datatypes ((ChannelBuf<Int> 0)) ((par () ((insert (head Int) (tail ChannelBuf<Int>)) (nilBuf)))))

; adt definitions
(declare-datatypes ((%Mutex 0)) ((par () (
  %Mutex-0))))

; monomorphized tuple definitions for mutable references
(declare-datatypes ((~Mut<Int> 0)) ((par () ((~mut<Int> (~cur<Int> Int) (~ret<Int> Int))))))

; library definitions
(declare-fun MergeInt (ChannelBuf<Int> ChannelBuf<Int> ChannelBuf<Int>) Bool)
(assert (MergeInt nilBuf nilBuf nilBuf))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt (insert n x1) x2 (insert n x)))))
(assert (forall ((x1 ChannelBuf<Int>) (x2 ChannelBuf<Int>) (x ChannelBuf<Int>) (n Int))
  (=> (MergeInt x1 x2 x) (MergeInt x1 (insert n x2) (insert n x)))))

; functions
(declare-fun %main (Bool) Bool)
(declare-fun %main.9 (Int LockHistory<Int> LockHistory<Int> LockHistory<Int> ~Mut<Int> ~Mut<Int> Bool Bool) Bool)

; %main
(assert (forall ((_! Bool) (_?.0 Int) (_@0.1 LockHistory<Int>) (_*.2_4 LockHistory<Int>) (_@0.2 LockHistory<Int>) (_*.3_4 LockHistory<Int>) (_@0.3 LockHistory<Int>) (_@0.4 ~Mut<Int>) (_*.4_4 LockHistory<Int>) (_@0.6 ~Mut<Int>) (_*.6_4 LockHistory<Int>) (_@0.8 ~Mut<Int>) (_*.8_7 LockHistory<Int>) (_%.nonce LockHistory<Int>)) (=>
  (and (Consistent _?.0 _@0.1) (MergeLock _*.2_4 _@0.2 _@0.1) (MergeLock _*.3_4 _@0.3 _@0.2) (= _*.2_4 (insertLock _@0.4 _*.4_4)) (= _*.4_4 nilHistory) (= _*.3_4 (insertLock _@0.6 _*.6_4)) (= _*.6_4 nilHistory) (= _@0.3 (insertLock _@0.8 _*.8_7)) (= (~ret<Int> _@0.8) (~cur<Int> _@0.8)) (%main.9 _?.0 _%.nonce _%.nonce _*.8_7 (~mut<Int> (+ (~cur<Int> _@0.4) 1) (~ret<Int> _@0.4)) (~mut<Int> (+ (~cur<Int> _@0.6) 2) (~ret<Int> _@0.6)) (>= (~cur<Int> _@0.8) _?.0) _!))
  (%main _!))))
; %main bb9
(assert (forall ((_1 Int) (_2 LockHistory<Int>) (_4 LockHistory<Int>) (_6 LockHistory<Int>) (_8 ~Mut<Int>) (_13 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _8) (~cur<Int> _8)) (= (~ret<Int> _13) (~cur<Int> _13)) (= _! true))
  (%main.9 _1 _2 _4 _6 _8 _13 false _!))))
(assert (forall ((_1 Int) (_2 LockHistory<Int>) (_4 LockHistory<Int>) (_6 LockHistory<Int>) (_8 ~Mut<Int>) (_13 ~Mut<Int>) (_! Bool)) (=>
  (and (= (~ret<Int> _13) (~cur<Int> _13)) (= (~ret<Int> _8) (~cur<Int> _8)) (= _! false))
  (%main.9 _1 _2 _4 _6 _8 _13 true _!))))

(assert (forall ((_% Int)) (=> (%main true) false)))
(check-sat)
