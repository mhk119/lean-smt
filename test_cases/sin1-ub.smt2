; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)

(assert (< (sin 0.5) 0.478))


(check-sat)
