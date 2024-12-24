(set-logic LIA)
(define-fun max2 ((x Int)(y Int)) Int
    (ite (>= y x) y x)
)

(assert (forall ((x Int)(y Int))
           (>= (max2 x y) x)))
(assert (forall ((x Int)(y Int))
           (>= (max2 x y) y)))
(assert (forall ((x Int)(y Int))
           (or (= x (max2 x y)) (= y (max2 x y)))))
(check-sat)
