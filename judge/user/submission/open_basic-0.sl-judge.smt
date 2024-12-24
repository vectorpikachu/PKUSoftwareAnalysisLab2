(set-logic BV)
(define-fun shr1 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvlshr x #x0000000000000001)
)

(define-fun shr4 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvlshr x #x0000000000000004)
)

(define-fun shr16 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvlshr x #x0000000000000010)
)

(define-fun shl1 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvshl x #x0000000000000001)
)

(define-fun if0 ((x (_ BitVec 64))(y (_ BitVec 64))(z (_ BitVec 64))) (_ BitVec 64)
    (ite (= x #x0000000000000001) y z)
)

(define-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor x #x0000000000000001)
)

(assert (= (f #x0000000000000010) #x0000000000000011))
(check-sat)
