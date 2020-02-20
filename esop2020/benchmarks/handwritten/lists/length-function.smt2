(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun length ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (length nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (length xs n) (length (insert x xs) (+ 1 n)))
))

(assert (forall ((m Int) (n Int) (xs (List Int)))
  (=> (and (length xs m) (length xs n))
    (= m n))
))

(check-sat) ; sat successfully
(get-model)
