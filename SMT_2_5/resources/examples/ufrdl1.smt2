(set-logic QF_UFRDL)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun f (Real) Real)

(assert (distinct (f x) (f y)))

(assert (<= (- x y) 0))

(check-sat)
(get-model)