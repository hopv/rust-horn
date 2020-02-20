(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun some ((Mut (List Int)) (Mut Int)) Bool)
(assert (forall ((x Int) (x! Int) (xs (List Int)))
  (=> true
    (some (mut (insert x xs) (insert x! xs)) (mut x x!)))
))
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)) (mr (Mut Int)))
  (=> (some (mut xs xs!) mr)
    (some (mut (insert x xs) (insert x xs!)) mr))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (k Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int) (y! Int))
  (=> (and (sum xs n) (some (mut xs xs!) (mut y y!)) (= y! (+ y k)) (sum xs! r))
    (= r (+ n k)))
))

(check-sat) ; timeout
(get-model)
