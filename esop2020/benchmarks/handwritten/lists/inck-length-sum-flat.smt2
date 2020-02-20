(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun inck ((List Int) (List Int) Int) Bool)
(assert (forall ((k Int))
  (=> true
    (inck nil nil k))
))
(assert (forall ((k Int) (x Int) (xs (List Int)) (xs! (List Int)))
  (=> (inck xs xs! k)
    (inck (insert x xs) (insert (+ x k) xs!) k))
))

(declare-fun length ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (length nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (length xs n) (length (insert x xs) (+ 1 n)))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (l Int) (r Int) (k Int) (xs (List Int)) (xs! (List Int)))
  (=> (and (sum xs n) (length xs l) (inck xs xs! k) (sum xs! r))
    (= r (+ n (* k l))))
))

(check-sat) ; unsat unsoundly
(get-model)
