(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun someleaf ((Tree Int) (Tree Int) (Tree Int) (Tree Int)) Bool)
(assert (forall ((tx! (Tree Int)))
  (=> true (someleaf leaf tx! leaf tx!))
))
(assert (forall ((txl (Tree Int)) (txl! (Tree Int)) (x Int) (txr (Tree Int)) (tr (Tree Int)) (tr! (Tree Int)))
  (=> (someleaf txl txl! tr tr!) (someleaf (node txl x txr) (node txl! x txr) tr tr!))
))
(assert (forall ((txl (Tree Int)) (x Int) (txr (Tree Int)) (txr! (Tree Int)) (tr (Tree Int)) (tr! (Tree Int)))
  (=> (someleaf txr txr! tr tr!) (someleaf (node txl x txr) (node txl x txr!) tr tr!))
))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((m Int) (n Int) (r Int) (tx (Tree Int)) (tx! (Tree Int)) (ty (Tree Int)) (tz (Tree Int)) (tz! (Tree Int)) (y Int) (y! Int))
  (=> (and (sum tx m) (sum ty n) (someleaf tx tx! tz tz!) (= tz! ty) (sum tx! r))
    (= r (+ m n)))
))

(check-sat) ; sat successfully
(get-model)
