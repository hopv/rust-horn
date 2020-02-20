(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun back ((Mut (List Int)) (Mut (List Int))) Bool)
(assert (forall ((xs (List Int)))
  (=> true
    (back (mut nil xs) (mut nil xs)))
))
(assert (forall ((x Int) (xs (List Int)) (xs! (List Int)) (mrs (Mut (List Int))))
  (=> (back (mut xs xs!) mrs)
    (back (mut (insert x xs) (insert x xs!)) mrs))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (m Int) (r Int) (xs (List Int)) (xs! (List Int)) (ys (List Int)) (zs (List Int)) (zs! (List Int)))
  (=> (and (back (mut xs xs!) (mut zs zs!)) (= zs! ys) (sum xs n) (sum ys m) (sum xs! r))
    (= r (+ n m)))
))

(check-sat) ; timeout
(get-model)
