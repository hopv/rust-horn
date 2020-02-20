(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun prod ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (prod nil 1))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (prod xs n) (prod (insert x xs) (* x n)))
))

(assert (forall ((m Int) (n Int) (xs (List Int)))
  (=> (and (prod xs m) (prod xs n))
    (= m n))
))

(check-sat) ; sat successfully
(get-model)
