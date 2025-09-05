; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)

(assert (> (exp (- 1)) 0.368))


(check-sat)
