; Problem using ARITH_TRANS_SINE_BOUNDS
(set-logic ALL)

(declare-const t Real)

(assert (< (sin t) (- 1)))

(check-sat)
