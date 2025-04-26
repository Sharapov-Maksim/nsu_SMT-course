;sat
(set-logic QF_UFRDL)

(define-fun x () Real
    -3.5)
(define-fun y () Real
    1.0)
(define-fun z () Real
    -3.5)
(define-fun a () Real
    5.0)
(define-fun b () Real
    -0.5)
(define-fun f ((x!0 Real)) Real
    6.0)

(check-sat)
(get-model)