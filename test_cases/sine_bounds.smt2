; Problem using ARITH_TRANS_SINE_BOUNDS
(set-logic ALL)

(assert (> (sin 2.0) 1.0))

; (declare-const t Real)

; (assert (or (> (sin t) 1.0) (< (sin t) (- 1.0))))

(check-sat)
