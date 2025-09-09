/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_BELOW_NEGE
-/

import Smt.Reconstruct.Real.TransFns.ArithTransSineApproxBelowPos

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem arithTransSineApproxBelowNeg (d k : Nat) (hd : d =2*k + 1) (hx : x < 0) :
  let p : ℕ → ℝ → ℝ := fun d x => taylorWithinEval Real.sin d Set.univ 0 x - x ^ (d + 1) / (d + 1).factorial
  p d x ≤ sin x := by
  intro p; simp only [p]
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
  rw [←sub_nonneg, ←sub_add, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  rw [sub_zero, mul_div_assoc, ← add_one_mul]
  apply mul_nonneg _ _
  · rw [←neg_le_iff_add_nonneg', neg_le]; apply neg_one_le_iteratedDeriv_sin
  · apply mul_nonneg (le_of_lt (Even.pow_pos (by rw [hd]; norm_num) (by linarith))) (by simp [Nat.factorial_pos (d + 1)])

end Smt.Reconstruct.Real.TransFns
