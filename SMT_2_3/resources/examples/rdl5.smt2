;sat
(set-logic QF_RDL)

(define-fun x1 () Real
    0)
(define-fun x4 () Real
    6)
(define-fun x3 () Real
    5)
(define-fun x2 () Real
    3)

(check-sat)
(get-model)
