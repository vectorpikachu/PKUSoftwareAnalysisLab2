(set-logic LIA)
(define-fun findIdx ((y1 Int)(y2 Int)(k1 Int)) Int
    (ite (< k1 y1) 0 (ite (< k1 y2) 1 2))
)

(assert (forall ((k Int)(x1 Int)(x2 Int))
           (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0)))))
(assert (forall ((k Int)(x1 Int)(x2 Int))
           (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2)))))
(assert (forall ((k Int)(x1 Int)(x2 Int))
           (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1)))))
(check-sat)
