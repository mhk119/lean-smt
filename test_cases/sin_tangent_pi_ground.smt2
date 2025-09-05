(set-logic ALL)


(assert (<= (sin 1.0) (- (- real.pi) 1.0)))

(check-sat)
