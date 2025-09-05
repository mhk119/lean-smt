(set-logic ALL)

(declare-const t Real)

(assert (< t 0.0))
(assert (>= (exp t) 1.0))

(check-sat)
