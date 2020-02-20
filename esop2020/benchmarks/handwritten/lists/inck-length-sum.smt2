(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun inck ((Mut (List Int)) Int ) Bool)
(assert (forall ((k Int))
  (=> true
    (inck (mut nil nil) k))
))
(assert (forall ((k Int) (x Int) (xs (List Int)) (xs! (List Int)))
  (=> (inck (mut xs xs!) k)
    (inck (mut (insert x xs) (insert (+ x k) xs!)) k))
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

(assert (forall ((n Int) (l Int) (r Int) (k Int) (xs (List Int)) (xs! (List Int)))
  (=> (and (sum xs n) (length xs l) (inck (mut xs xs!) k) (sum xs! r))
    (= r (+ n (* k l))))
))

(check-sat) ; unsat unsoundly
(get-model)
