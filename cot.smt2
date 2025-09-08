(set-logic ALL)

(assert (= (cot (/ real.pi 2.0)) 0.1))

(check-sat)
