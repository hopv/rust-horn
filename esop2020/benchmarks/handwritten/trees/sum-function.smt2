(set-logic HORN)

(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((m Int) (n Int) (tx (Tree Int)))
  (=> (and (sum tx m) (sum tx n))
    (= m n))
))

(check-sat) ; sat successfully
(get-model)
