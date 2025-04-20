(set-logic QF_UF)
(declare-sort H 0)

(declare-fun x () H)
(declare-fun f (H) H)

(assert (= (f (f (f x))) x))
(assert (= (f (f (f (f (f x))))) x))
(assert (distinct (f x) x))

(check-sat)