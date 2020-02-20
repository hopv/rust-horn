(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun some ((List Int) (List Int) Int Int) Bool)
(assert (forall ((x Int) (x! Int) (xs (List Int)))
  (=> true
    (some (insert x xs) (insert x! xs) x x!))
))
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)) (r Int) (r! Int))
  (=> (some xs xs! r r!)
    (some (insert x xs) (insert x xs!) r r!))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (k Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int) (y! Int))
  (=> (and (sum xs n) (some xs xs! y y!) (= y! (+ y k)) (sum xs! r))
    (= r (+ n k)))
))

(check-sat) ; sat successfully
(get-model)
