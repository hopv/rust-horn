(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun append ((Mut (List Int)) (List Int)) Bool)
(assert (forall ((xs (List Int)))
  (=> true
    (append (mut nil xs) xs))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)))
  (=> (append (mut xs xs!) ys)
    (append (mut (insert x xs) (insert x xs!)) ys))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (m Int) (r Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)))
  (=> (and (sum xs n) (sum ys m) (append (mut xs xs!) ys) (sum xs! r))
    (= r (+ n m)))
))

(check-sat) ; timeout
(get-model)
