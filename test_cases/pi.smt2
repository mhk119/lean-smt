; COMMAND-LINE: --nl-ext=full -q
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(assert (not (or (<= 3.0 real.pi) (>= real.pi 4.0))))
(check-sat)
