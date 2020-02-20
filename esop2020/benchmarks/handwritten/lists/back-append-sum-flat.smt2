(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun back ((List Int) (List Int) (List Int) (List Int)) Bool)
(assert (forall ((xs (List Int)))
  (=> true
    (back nil xs nil xs))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (rs (List Int)) (rs! (List Int)))
  (=> (back xs xs! rs rs!)
    (back (insert x xs) (insert x xs!) rs rs!))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (m Int) (r Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)) (zs (List Int)) (zs! (List Int)))
  (=> (and (back xs xs! zs zs!) (= zs! ys) (sum xs n) (sum ys m) (sum xs! r))
    (= r (+ n m)))
))

(check-sat) ; sat successfully
(get-model)
