(set-logic LIA)
(define-fun qm ((a Int)(b Int)) Int
    (ite (< a 0) b a)
)

(define-fun qm-foo ((x Int)) Int
    (- x (qm x (- x 1)))
)

(assert (forall ((x Int))
           (= (qm-foo x) (ite (< x 0) 1 0))))
(check-sat)
