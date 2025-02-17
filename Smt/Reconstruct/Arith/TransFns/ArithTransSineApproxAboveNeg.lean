/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/


import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAbovePos
import Smt.Reconstruct.Arith.TransFns.ArithTransExpApproxAboveNeg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv


open Set Real

namespace Smt.Reconstruct.Arith

theorem iteratedDeriv_sin_cos (n : Nat) :
  (iteratedDeriv n sin =
    if n % 4 = 0 then sin else
    if n % 4 = 1 then cos else
    if n % 4 = 2 then -sin else
    -cos) ∧
    (iteratedDeriv n cos =
    if n % 4 = 0 then cos else
    if n % 4 = 1 then -sin else
    if n % 4 = 2 then -cos else
    sin) := by
  induction' n with n ih
  · simp [iteratedDeriv]
  · simp [ih.1, ih.2, iteratedDeriv_succ']
    have :=  Nat.mod_lt n (show 4 > 0 by decide)
    interval_cases hn : n % 4
    <;> simp [hn, Nat.add_mod]
    <;> ext
    <;> simp [iteratedDeriv_neg, ih]

-- #check strictConcaveOn_sin_Icc
-- #check neg_convexOn_iff

-- theorem jjsj {𝕜 : Type u_1} {E : Type u_2} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E} :
-- Convex 𝕜 s ↔ Convex 𝕜 (-s) := sorry

-- example {s : Set ℝ} {f : ℝ → ℝ}: StrictConvexOn ℝ s f ↔ StrictConvexOn ℝ (-s) f := by
--   simp [StrictConvexOn, neg_convexOn_iff]
--   simp [← jjsj]

theorem convexOn_sin_Icc : ConvexOn ℝ (Icc (-π) 0) sin := by
  apply StrictConvexOn.convexOn
  rw [← neg_strictConcaveOn_iff]
  rw [← neg_strictConvexOn_iff]
  simp only [neg_neg]
  sorry

  --
  -- apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  -- rw [interior_Icc] at hx
  -- simp [sin_pos_of_mem_Ioo hx]

  -- apply ConvexOn.of_strictConvexOn_Ioo
  -- apply strictConvexOn_sin_Ioo

theorem sineApproxAboveNeg (d k : Nat) (hd : d = 4*k + 3) (hx : x < 0) (hx2 : -π ≤ x):
  let p : ℕ → ℝ → ℝ := fun d => taylorWithinEval Real.sin d Set.univ 0
  sin x ≤ p d x := by
  intro p
  have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ (n := d) hx contDiff_sin
  rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
  rw [←sub_nonpos, H]
  rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
  have : (d+1)%4 = 0 := by simp [hd, Nat.add_mod]
  simp only [this, iteratedDeriv_sin_cos, reduceIte, three_ne_zero, sub_zero, show 3 ≠ 1 by decide, show 3 ≠ 0 by decide, show 3 ≠ 2 by decide]
  apply mul_nonpos_of_nonpos_of_nonneg _ (by apply inv_nonneg.mpr; simp)
  apply mul_nonpos_of_nonpos_of_nonneg (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (le_of_lt (mem_Ioo.mp hx').2) (le_trans hx2 (le_of_lt (mem_Ioo.mp hx').1)))
  apply Even.pow_nonneg (by rw [even_iff_two_dvd]; omega)

theorem arithTransSineApproxAboveNeg (d k : Nat) (hd : d = 4*k + 3) (l u t : ℝ)
                                     (ht : l ≤ t ∧ t ≤ u) (hu : u < 0) (hl : -π ≤ l) :
  let p: ℝ → ℝ := taylorWithinEval Real.sin d Set.univ 0
  Real.sin t ≤ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.sin d Set.univ 0 x := by simp
  apply le_convex_of_le ht
        (by rw [hp]; exact sineApproxAboveNeg d k hd (by linarith) hl)
        (by rw [hp]; exact sineApproxAboveNeg d k hd hu (by linarith))
        convexOn_sin_Icc (mem_Icc.mpr ⟨hl, by linarith⟩)
                         (mem_Icc.mpr ⟨by linarith, le_of_lt hu⟩)
