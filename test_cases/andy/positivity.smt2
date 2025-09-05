; Problem using ARITH_TRANS_EXP_POSITIVITY
(set-logic ALL)

(declare-const t Real)

(assert (<= (exp t) 0.0))

(check-sat)
