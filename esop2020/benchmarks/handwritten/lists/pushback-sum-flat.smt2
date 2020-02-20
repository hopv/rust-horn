(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun pushback ((List Int) (List Int) Int) Bool)
(assert (forall ((x Int))
  (=> true
    (pushback nil (insert x nil) x))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (y Int))
  (=> (pushback xs xs! y)
    (pushback (insert x xs) (insert x xs!) y))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int))
  (=> (and (sum xs n) (pushback xs xs! y) (sum xs! r))
    (= r (+ n y)))
))

(check-sat) ; sat successfully
(get-model)
