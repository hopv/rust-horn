(set-logic HORN)

(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun some-rest ((List Int) (List Int) Int Int (List Int) (List Int)) Bool)
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)))
  (=> true
    (some-rest (insert x xs) (insert x! xs!) x x! xs xs!))
))
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)) (y Int) (y! Int) (zs (List Int)) (zs! (List Int)))
  (=> (some-rest xs xs! y y! zs zs!)
    (some-rest (insert x xs) (insert x xs!) y y! zs zs!))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (k Int) (k2 Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int) (y! Int) (zs (List Int)) (zs! (List Int)) (w Int) (w! Int) (vs (List Int)))
  (=> (and (sum xs n) (some-rest xs xs! y y! zs zs!)
           (some-rest zs zs! w w! vs vs) (= y! (+ y k)) (= w! (+ w k2)) (sum xs! r))
    (= r (+ n k k2)))
))

(check-sat) ; timeout
(get-model)
