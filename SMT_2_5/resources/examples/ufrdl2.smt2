;sat
(set-logic QF_UFRDL)

(define-fun x () Real
    0.0)
(define-fun y () Real
    1.0)
(define-fun f ((x!0 Real)) Real
    (ite (= x!0 0.0) 0.0
        (ite (= x!0 1.0) 1.0
            0.0)))

(check-sat)
(get-model)