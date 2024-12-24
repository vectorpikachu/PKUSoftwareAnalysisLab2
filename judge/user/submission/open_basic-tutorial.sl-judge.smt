(set-logic LIA)
(define-fun rec ((x Int)(y Int)(z Int)) Int
    (* (+ x x) (- y z))
)

(assert (forall ((x1 Int)(x2 Int)(x3 Int))
           (= (rec x1 x2 x3) (* (+ x1 x1) (- x2 x3)))))
(check-sat)
