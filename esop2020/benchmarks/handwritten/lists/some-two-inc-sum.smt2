(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun some-rest ((Mut (List Int)) (Mut Int) (Mut (List Int))) Bool)
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)))
  (=> true
    (some-rest (mut (insert x xs) (insert x! xs!)) (mut x x!) (mut xs xs!)))
))
(assert (forall ((x Int) (x! Int) (xs (List Int)) (xs! (List Int)) (my (Mut Int)) (mzs (Mut (List Int))))
  (=> (some-rest (mut xs xs!) my mzs)
    (some-rest (mut (insert x xs) (insert x xs!)) my mzs))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (k Int) (k2 Int) (r Int) (xs (List Int)) (xs! (List Int)) (y Int) (y! Int) (zs (List Int)) (zs! (List Int)) (w Int) (w! Int) (vs (List Int)))
  (=> (and (sum xs n) (some-rest (mut xs xs!) (mut y y!) (mut zs zs!))
           (some-rest (mut zs zs!) (mut w w!) (mut vs vs)) (= y! (+ y k)) (= w! (+ w k2)) (sum xs! r))
    (= r (+ n k k2)))
))

(check-sat) ; buggy error
(get-model)
