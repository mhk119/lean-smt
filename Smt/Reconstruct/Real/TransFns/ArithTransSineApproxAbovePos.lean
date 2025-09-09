/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_ABOVE_POSE
-/

import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowNeg

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineApproxAbovePos (d k : ℕ) (hd : d = 2*k + 1)
                                     (hx : 0 < x) (hx2 : x ≤ π) :
    Real.sin x ≤ taylorWithinEval Real.sin d Set.univ 0 x + x ^ (d + 1) / (d + 1).factorial := by
  rw [← neg_neg x, sin_neg, taylorSin_neg, neg_add_eq_sub, ←neg_sub, neg_le_neg_iff, Even.neg_pow (by rw [hd]; norm_num)]
  apply arithTransSineApproxBelowNeg d k hd (by linarith) (by linarith)

end Smt.Reconstruct.Real.TransFns
