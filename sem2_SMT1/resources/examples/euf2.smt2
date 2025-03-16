(set-logic QF_UF)
(declare-sort H 0)

(declare-fun a () H)
(declare-fun b () H)
(declare-fun c () H)
(declare-fun f (H) H)
(declare-fun g (H H) H)

(assert (= a b))
(assert (= b c))
(assert (= (g (f a) b) (g (f c) a)))
(assert (distinct (f a) b))

(check-sat)
(get-model)
(get-value (a))
(get-value (b))
(get-value (c))