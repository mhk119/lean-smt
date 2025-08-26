(set-logic ALL)

(declare-const x1 Real)
(declare-const x2 Real)
(declare-const y1 Real)
(declare-const y2 Real)

(assert (> (abs x1) (abs y1)))
(assert (> (abs x2) (abs y2)))

(assert (<= (abs (* x1 x2)) (abs (* y1 y2))))


(check-sat)
