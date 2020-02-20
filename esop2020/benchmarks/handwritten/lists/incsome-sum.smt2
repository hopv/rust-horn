(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((List 1)) ((par (T) (nil (insert (head T) (tail (List T)))))))

(declare-fun incsome (Int (Mut (List Int))) Bool)
(assert (forall ((k Int) (x Int) (xs (List Int)) (xs! (List Int)))
  (=> true
    (incsome k (mut (insert x xs) (insert (+ x k) xs))))
))
(assert (forall ((k Int) (x Int) (xs (List Int)) (xs! (List Int)))
  (=> (incsome k (mut xs xs!))
    (incsome k (mut (insert x xs) (insert x xs!))))
))

(declare-fun sum ((List Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum nil 0))
))
(assert (forall ((n Int) (x Int) (xs (List Int)))
  (=> (sum xs n) (sum (insert x xs) (+ x n)))
))

(assert (forall ((n Int) (k Int) (r Int) (xs (List Int)) (xs! (List Int)))
  (=> (and (sum xs n) (incsome k (mut xs xs!)) (sum xs! r))
    (= r (+ n k)))
))

(check-sat) ; sat successfully
(get-model)
