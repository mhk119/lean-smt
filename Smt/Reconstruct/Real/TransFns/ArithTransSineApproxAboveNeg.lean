/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule33ARITH_TRANS_SINE_APPROX_ABOVE_NEGE
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAbovePos
import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxAboveNeg
import Smt.Reconstruct.Real.TransFns.Utils

open Set Real

namespace Smt.Reconstruct.Real.TransFns

example (a b : Real) (h : a ≤ b): a -b ≤ 0:= by
  exact tsub_nonpos.mpr h

theorem sineApproxAboveNeg (d k : Nat) (hd : d =2*k + 1) (hx : x < 0):
  let p : ℕ → ℝ → ℝ := fun d x => taylorWithinEval Real.sin d Set.univ 0 x + (x ^ (d + 1)) / (d + 1).factorial
  sin x ≤ p d x := by
  intro p; simp only [p]
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
  rw [←sub_nonpos, sub_add_eq_sub_sub, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  rw [sub_zero, mul_div_assoc, ← sub_one_mul]
  apply mul_nonpos_of_nonpos_of_nonneg _ _
  · rw [tsub_nonpos]; apply iteratedDeriv_sin_le_one
  · apply mul_nonneg (le_of_lt (Even.pow_pos (by rw [hd]; norm_num) (by linarith))) (by simp [Nat.factorial_pos (d + 1)])

theorem arithTransSineApproxAboveNeg (d k : Nat) (hd : d = 2*k + 1) (l u t : ℝ)
                                     (ht : l ≤ t ∧ t ≤ u) (hu : u < 0) (hl : -π ≤ l) :
  let p: ℝ → ℝ := fun x => taylorWithinEval Real.sin d Set.univ 0 x + (x ^ (d + 1)) / (d + 1).factorial
  Real.sin t ≤ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p; simp only [p]
  apply le_convex_of_le ht
        (sineApproxAboveNeg d k hd (by linarith))
        (sineApproxAboveNeg d k hd hu)
        convexOn_sin_Icc (mem_Icc.mpr ⟨hl, by linarith⟩)
                         (mem_Icc.mpr ⟨by linarith, le_of_lt hu⟩)

end Smt.Reconstruct.Real.TransFns
