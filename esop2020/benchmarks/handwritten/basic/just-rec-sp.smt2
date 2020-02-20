(set-logic HORN)

(declare-fun just-rec (Int (Array Int Int) Int (Array Int Int) Int Bool) Bool)
(assert (forall ((ma Int) (h (Array Int Int)) (sp Int))
  (just-rec ma h sp h sp true)))
(assert (forall ((ma Int) (mb Int) (h (Array Int Int)) (h! (Array Int Int)) (h!! (Array Int Int)) (sp Int) (sp! Int) (sp!! Int) (r Bool) (_r Bool) (b Int))
  (=> (and
      (= sp! (+ sp 1)) (= mb sp!) (= h! (store h sp! b))
      (just-rec mb h! sp! h!! sp!! _r)
      (= r (= (select h ma) (select h!! ma))))
    (just-rec ma h sp h!! sp!! r))))
(assert (forall ((ma Int) (h (Array Int Int)) (h! (Array Int Int)) (sp Int) (sp! Int) (r Bool))
  (=> (and (just-rec ma h sp h! sp! r) (<= ma sp))
    (= r true))))

(check-sat) ; got timeout, expecting sat
(get-model)
