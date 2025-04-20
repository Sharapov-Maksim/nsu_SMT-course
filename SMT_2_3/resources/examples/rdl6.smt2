;sat
(set-logic QF_RDL)

(define-fun x1 () Real
    0)
(define-fun x4 () Real
    5.9)
(define-fun x3 () Real
    4.9)
(define-fun x2 () Real
    2.9)

(check-sat)
(get-model)