; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)

(assert (< (sin 2.0) 0.8))


(check-sat)
