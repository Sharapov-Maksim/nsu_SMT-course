(set-logic QF_UF)

(declare-sort H 0)

(declare-fun a () H)
(declare-fun b () H)
(declare-fun f (H H) H)

(assert (= (f a b) a))

(assert (distinct (f (f a b) b) a))

(check-sat)