/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Tomaz Gomes
-/


import Smt.Reconstruct.Arith.TransFns.ArithTransSineApproxAboveNeg

open Set Real

namespace Smt.Reconstruct.Arith


theorem sineApproxBelowPos (d k : Nat) (hd : d = 4*k + 3)
                           (hx : 0 < x) (hx2 : x ≤ π) :
  let p : ℕ → ℝ → ℝ := fun d => taylorWithinEval Real.sin d Set.univ 0
  p d x ≤ sin x:= by
  intro p
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange (n := d) hx
                        (ContDiff.contDiffOn contDiff_sin)
                        (DifferentiableOn_iteratedDerivWithin (contDiff_sin) hx)
  rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
  rw [←sub_nonneg, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  have : (d+1)%4 = 0 := by simp [hd, Nat.add_mod]
  simp only [this, iteratedDeriv_sin_cos, reduceIte, three_ne_zero, sub_zero, show 3 ≠ 1 by decide, show 3 ≠ 0 by decide, show 3 ≠ 2 by decide]
  apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
  apply mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt ((mem_Ioo.mp hx').1)) (le_trans (le_of_lt (mem_Ioo.mp hx').2) hx2)) (pow_nonneg (le_of_lt hx) _)

theorem iteratedDerivWithin_sin_eq_zero_of_even (j : ℕ) (hj : Even j) :
  iteratedDerivWithin j sin univ 0 = 0 := by
  have := Nat.mod_lt j (show 4 > 0 by decide)
  interval_cases h : j % 4
  <;> rw [← Even.mod_even_iff (show Even 4 by decide), h] at hj
  <;> try {simp only [show ¬ Even 3 by decide, Nat.not_even_one] at hj}
  <;> rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin uniqueDiffOn_univ 0 (Set.mem_univ 0)]
  <;> simp [iteratedDeriv_sin_cos, h]

theorem taylorSin_neg (x : Real):
  let p: ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
  p (-x) = -p x := by
  intro p
  simp only [p, taylor_within_apply, sub_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  cases' (Nat.even_or_odd j) with h h
  · rw [iteratedDerivWithin_sin_eq_zero_of_even j h]
    simp
  · rw [Odd.neg_pow h]
    simp

theorem arithTransSineApproxBelowPos (d k : Nat) (hd : d = 4*k + 3) (l u t : ℝ)
                                     (ht : l ≤ t ∧ t ≤ u) (hu : u ≤ π) (hl : 0 < l) :
  let p: ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
  ((p l - p u) / (l - u)) * (t - l) + p l ≤ Real.sin t:= by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.sin d Set.univ 0 x := by simp
  rw [hp, hp, ← neg_neg t, ← neg_neg l, ← neg_neg u, sin_neg, taylorSin_neg (-l), taylorSin_neg (-u), ←neg_le_neg_iff]
  simp only [neg_neg, sub_neg_eq_add, neg_add_rev]
  rw [←neg_mul, neg_div', neg_add, neg_neg, add_comm, ←hp, ←hp]
  rw [show t- l = -(-t -(-l)) by ring, show l-u = -(-l-(-u)) by ring, div_mul_neg]
  apply le_convex_of_le' ⟨by linarith, by linarith⟩
        (by rw [hp]; exact sineApproxAboveNeg d k hd (by linarith) (by linarith))
        (by rw [hp]; exact sineApproxAboveNeg d k hd (by linarith) (by linarith))
        convexOn_sin_Icc (mem_Icc.mpr ⟨by linarith, by linarith⟩)
                         (mem_Icc.mpr ⟨by linarith, by linarith⟩)
