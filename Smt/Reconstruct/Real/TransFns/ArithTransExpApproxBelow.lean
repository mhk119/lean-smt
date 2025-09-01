/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule28ARITH_TRANS_EXP_APPROX_BELOWE
-/

import Smt.Reconstruct.Real.TransFns.Utils

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem iteratedDeriv_exp (n : Nat) : iteratedDeriv n exp = exp := by
    induction' n with n hn
    · simp
    · simp [iteratedDeriv_succ, hn]

theorem DifferentiableOn_iteratedDerivWithin {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hx : a < b) :
    DifferentiableOn ℝ (iteratedDerivWithin d f (Icc a b)) (Ioo a b) := by
    apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
    apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
    apply ContDiff.contDiffOn (by apply ContDiff.of_le hf (by norm_cast; simp))

-- can definitely be shortened. same proof below
theorem arithTransExpApproxBelow₁ (x : ℝ) (d n : ℕ) (_ : d = 2 * n + 1) (hx : 0 < x) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have h2 : DifferentiableOn ℝ (iteratedDerivWithin d rexp (Icc 0 x)) (Ioo 0 x) := by
        apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
        apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
        apply ContDiff.contDiffOn ((contDiff_infty.mp contDiff_exp) _)
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange hx (ContDiff.contDiffOn (s := Icc 0 x) (n := d) contDiff_exp) h2
    rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x')) (by simp [le_of_lt hx])


-- see the last line. this probably holds for any function.
theorem arithTransExpApproxBelow₂ (x : ℝ) (d n : ℕ) (h : d = 2 * n + 1) (hx : x < 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ hx contDiff_exp (n := d)
    rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x'))
    apply Even.pow_nonneg; rw [h, show 2*n + 1 + 1 = 2*(n+1) by ring]; simp

theorem arithTransExpApproxBelow₃ (x : ℝ) (d n : ℕ) (_ : d = 2 * n + 1) (hx : x = 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
  rw [hx]
  simp

theorem arithTransExpApproxBelow (x : ℝ) (d n : ℕ) (h : d = 2 * n + 1) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
  if hx : x < 0 then
    exact arithTransExpApproxBelow₂ x d n h hx
  else if hx2 : x = 0 then
    exact arithTransExpApproxBelow₃ x d n h hx2
  else
    have : 0 < x := by push_neg at *; exact lt_of_le_of_ne hx (id (Ne.symm hx2))
    exact arithTransExpApproxBelow₁ x d n h this

end Smt.Reconstruct.Real.TransFns

