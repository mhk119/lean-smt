; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)

(assert (< (sin 3.0) 0.140))


(check-sat)
