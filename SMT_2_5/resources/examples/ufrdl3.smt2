(set-logic QF_UFRDL)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun f (Real) Real)

(assert (<= (- x y) -3.5))
(assert (<= (- y z) 3.5))
(assert (<= (- z x) 0))
(assert (<= (- a b) 5.5))
(assert (= (f a) (f z)))
(assert (distinct (f a) (f x)))

(check-sat)