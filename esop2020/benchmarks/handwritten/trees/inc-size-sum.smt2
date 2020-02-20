(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun inc ((Mut (Tree Int))) Bool)
(assert (forall ((dummy Int))
  (=> true (inc (mut leaf leaf)))
))
(assert (forall ((txl (Tree Int)) (txl! (Tree Int)) (x Int) (txr (Tree Int)) (txr! (Tree Int)))
  (=> (and (inc (mut txl txl!)) (inc (mut txr txr!))) (inc (mut (node txl x txr) (node txl! (+ x 1) txr!))))
))

(declare-fun size ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (size leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (size txl m) (size txr n)) (size (node txl x txr) (+ m 1 n)))
))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((n Int) (s Int) (r Int) (tx (Tree Int)) (tx! (Tree Int)) (y Int) (y! Int))
  (=> (and (sum tx n) (size tx s) (inc (mut tx tx!)) (sum tx! r))
    (= r (+ n s)))
))

(check-sat) ; sat successfully
(get-model)
