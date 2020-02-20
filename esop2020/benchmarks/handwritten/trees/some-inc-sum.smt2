(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun some ((Mut (Tree Int)) (Mut Int)) Bool)
(assert (forall ((txl (Tree Int)) (x Int) (x! Int) (txr (Tree Int)))
  (=> true (some (mut (node txl x txr) (node txl x! txr)) (mut x x!)))
))
(assert (forall ((txl (Tree Int)) (txl! (Tree Int)) (x Int) (txr (Tree Int)) (mr (Mut Int)))
  (=> (some (mut txl txl!) mr) (some (mut (node txl x txr) (node txl! x txr)) mr))
))
(assert (forall ((txl (Tree Int)) (x Int) (txr (Tree Int)) (txr! (Tree Int)) (mr (Mut Int)))
  (=> (some (mut txr txr!) mr) (some (mut (node txl x txr) (node txl x txr!)) mr))
))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((n Int) (k Int) (r Int) (tx (Tree Int)) (tx! (Tree Int)) (y Int) (y! Int))
  (=> (and (sum tx n) (some (mut tx tx!) (mut y y!)) (= y! (+ y k)) (sum tx! r))
    (= r (+ n k)))
))

(check-sat) ; buggy error
(get-model)
