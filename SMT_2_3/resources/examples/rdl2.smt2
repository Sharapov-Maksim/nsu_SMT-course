(set-logic QF_RDL)

(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)

(assert (<= (- x1 x3) -5))
(assert (<= (- x1 x4) -3))
(assert (<= (- x2 x1) 3))
(assert (<= (- x3 x2) 2))
(assert (<= (- x3 x4) -1))
(assert (<= (- x4 x2) 5))

(check-sat)
(get-model)