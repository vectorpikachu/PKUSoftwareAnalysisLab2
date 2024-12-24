(set-logic LIA)
(define-fun max3 ((x Int)(y Int)(z Int)) Int
    (ite (>= z (ite (>= y x) y x)) z (ite (>= y x) y x))
)

(assert (forall ((x Int)(y Int)(z Int))
           (>= (max3 x y z) x)))
(assert (forall ((x Int)(y Int)(z Int))
           (>= (max3 x y z) y)))
(assert (forall ((x Int)(y Int)(z Int))
           (>= (max3 x y z) z)))
(assert (forall ((x Int)(y Int)(z Int))
           (or (= x (max3 x y z)) (or (= y (max3 x y z)) (= z (max3 x y z))))))
(check-sat)
