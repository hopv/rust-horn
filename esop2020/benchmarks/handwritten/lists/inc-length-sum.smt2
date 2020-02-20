(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun inc ((Mut (List Int))) Bool)
(assert (forall ((dummy Int))
  (=> true
    (inc (mut nil nil)))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)))
  (=> (inc (mut xs xs!))
    (inc (mut (insert x xs) (insert (+ x 1) xs!))))
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

(assert (forall ((n Int) (l Int) (r Int) (xs (List Int)) (xs! (List Int)))
  (=> (and (sum xs n) (length xs l) (inc (mut xs xs!)) (sum xs! r))
    (= r (+ n l)))
))

(check-sat) ; sat successfully
(get-model)
