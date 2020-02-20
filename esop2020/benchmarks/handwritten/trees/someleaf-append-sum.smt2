(set-logic HORN)

(declare-datatypes ((Mut 1)) ((par (T) ((mut (cur T) (ret T))))))
(declare-datatypes ((Tree 1)) ((par (T) (leaf (node (left (Tree T)) (value T) (right (Tree T)))))))

(declare-fun someleaf ((Mut (Tree Int)) (Mut (Tree Int))) Bool)
(assert (forall ((tx! (Tree Int)))
  (=> true (someleaf (mut leaf tx!) (mut leaf tx!)))
))
(assert (forall ((txl (Tree Int)) (txl! (Tree Int)) (x Int) (txr (Tree Int)) (mtr (Mut (Tree Int))))
  (=> (someleaf (mut txl txl!) mtr) (someleaf (mut (node txl x txr) (node txl! x txr)) mtr))
))
(assert (forall ((txl (Tree Int)) (x Int) (txr (Tree Int)) (txr! (Tree Int)) (mtr (Mut (Tree Int))))
  (=> (someleaf (mut txr txr!) mtr) (someleaf (mut (node txl x txr) (node txl x txr!)) mtr))
))

(declare-fun sum ((Tree Int) Int) Bool)
(assert (forall ((dummy Int))
  (=> true (sum leaf 0))
))
(assert (forall ((m Int) (n Int) (x Int) (txl (Tree Int)) (txr (Tree Int)))
  (=> (and (sum txl m) (sum txr n)) (sum (node txl x txr) (+ m x n)))
))

(assert (forall ((m Int) (n Int) (r Int) (tx (Tree Int)) (tx! (Tree Int)) (ty (Tree Int)) (tz (Tree Int)) (tz! (Tree Int)) (y Int) (y! Int))
  (=> (and (sum tx m) (sum ty n) (someleaf (mut tx tx!) (mut tz tz!)) (= tz! ty) (sum tx! r))
    (= r (+ m n)))
))

(check-sat) ; unknown, with sat expected
(get-model)
