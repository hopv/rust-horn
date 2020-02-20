(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun append ((List Int) (List Int) (List Int)) Bool)
(assert (forall ((xs (List Int)))
  (=> true
    (append nil xs xs))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)))
  (=> (append xs xs! ys)
    (append (insert x xs) (insert x xs!) ys))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (m Int) (r Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)))
  (=> (and (sum xs n) (sum ys m) (append xs xs! ys) (sum xs! r))
    (= r (+ n m)))
))

(check-sat) ; sat successfully
(get-model)
