(set-logic QF_UF)
(declare-sort H 0)

(declare-fun a () H)
(declare-fun b () H)
(declare-fun f (H) H)

(assert (distinct (f a) (f b)))

(check-sat)
(get-model)