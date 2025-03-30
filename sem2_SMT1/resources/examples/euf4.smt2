(set-logic QF_UF)

(declare-sort H 0)

(declare-fun a () H)
(declare-fun f (H) H)

(assert (= (f (f a)) a))

(assert (distinct (f a) a))

(check-sat)
(get-model)