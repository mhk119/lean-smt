; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)

(assert (> (exp 1) 2.719))


(check-sat)
