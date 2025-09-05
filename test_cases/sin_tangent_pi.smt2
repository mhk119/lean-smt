(set-logic ALL)

(declare-const t Real)

(assert (> t (- real.pi)))
(assert (<= (sin t) (- (- real.pi) t)))

(check-sat)
