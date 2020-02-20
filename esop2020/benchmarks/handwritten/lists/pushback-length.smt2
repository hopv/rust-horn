(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun pushback ((Mut (List Int)) Int) Bool)
(assert (forall ((x Int))
  (=> true
    (pushback (mut nil (insert x nil)) x))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (y Int))
  (=> (pushback (mut xs xs!) y)
    (pushback (mut (insert x xs) (insert x xs!)) y))
))

(declare-fun length ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (length nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (length xs n) (length (insert x xs) (+ 1 n)))
))

(assert (forall ((n Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int))
  (=> (and (length xs n) (pushback (mut xs xs!) y) (length xs! r))
    (= r (+ n 1)))
))

(check-sat) ; sat successfully
(get-model)
