(set-logic ALL)

(declare-const t Real)

(assert (> (sin 0.5) 0.5))

(check-sat)
