(set-logic HORN)

(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun prod ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (prod leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (prod txl m) (prod txr n)) (prod (node txl x txr) (* m x n)))
))

(assert (forall ((m Int) (n Int) (tx (Tree Int)))
  (=> (and (prod tx m) (prod tx n))
    (= m n))
))

(check-sat) ; sat successfully
(get-model)
