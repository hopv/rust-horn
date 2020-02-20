(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun inc&back ((List Int) (List Int) (List Int) (List Int)) Bool)
(assert (forall ((xs (List Int)))
  (=> true
    (inc&back nil xs nil xs))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (rs (List Int)) (rs! (List Int)))
  (=> (inc&back xs xs! rs rs!)
    (inc&back (insert x xs) (insert (+ x 1) xs!) rs rs!))
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

(assert (forall ((n Int) (m Int) (l Int) (r Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)) (zs (List Int)) (zs! (List Int)))
  (=> (and (sum xs n) (length xs l) (sum ys m) (inc&back xs xs! zs zs!) (= zs! ys) (sum xs! r))
    (= r (+ n l m)))
))

(check-sat) ; sat successfully
(get-model)
