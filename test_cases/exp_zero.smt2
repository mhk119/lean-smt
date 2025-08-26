(set-logic ALL)

(declare-const t Real)

(assert (not (= t 0)))
(assert (= (exp t) 1))

(check-sat)
