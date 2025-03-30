;sat
(set-logic QF_UF)
(declare-sort H 0)

(declare-fun H!val!1 () H)
(declare-fun H!val!0 () H)

(assert (distinct H!val!0 H!val!1))

(define-fun a () H
    H!val!0)
(define-fun f ((x!0 H)) H
    (ite (= x!0 H!val!1) H!val!0
        H!val!1))

(check-sat)
(get-model)