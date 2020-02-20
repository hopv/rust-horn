(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun some ((Tree Int) (Tree Int) Int Int) Bool)
(assert (forall ((txl (Tree Int)) (x Int) (x! Int) (txr (Tree Int)))
  (=> true (some (node txl x txr) (node txl x! txr) x x!))
))
(assert (forall ((txl (Tree Int)) (txl! (Tree Int)) (x Int) (txr (Tree Int)) (r Int) (r! Int))
  (=> (some txl txl! r r!) (some (node txl x txr) (node txl! x txr) r r!))
))
(assert (forall ((txl (Tree Int)) (x Int) (txr (Tree Int)) (txr! (Tree Int)) (r Int) (r! Int))
  (=> (some txr txr! r r!) (some (node txl x txr) (node txl x txr!) r r!))
))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((n Int) (k Int) (r Int) (tx (Tree Int)) (tx! (Tree Int)) (y Int) (y! Int))
  (=> (and (sum tx n) (some tx tx! y y!) (= y! (+ y k)) (sum tx! r))
    (= r (+ n k)))
))

(check-sat) ; sat successfully
(get-model)
