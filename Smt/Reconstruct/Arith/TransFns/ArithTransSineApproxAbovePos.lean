/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/


import Smt.Reconstruct.Arith.TransFns.ArithTransSineApproxBelowPos

open Set Real

namespace Smt.Reconstruct.Arith

theorem arithTransSineApproxAbovePos (d k : ℕ) (hd : d = 4*k + 1)
                                     (hx : 0 < x) (hx2 : x ≤ π) :
    Real.sin x ≤ taylorWithinEval Real.sin d Set.univ 0 x := by
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange (n := d) hx
                        (ContDiff.contDiffOn contDiff_sin)
                        (DifferentiableOn_iteratedDerivWithin (contDiff_sin) hx)
    rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) (contDiff_sin)] at H
    rw [←sub_nonpos, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_sin (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx')]
    have : (d+1)%4 = 2 := by simp [hd, Nat.add_mod]
    simp only [this, iteratedDeriv_sin_cos, reduceIte, one_ne_zero, sub_zero, show 1 ≠ 3 by decide, show 2 ≠ 1 by decide, two_ne_zero]
    apply mul_nonpos_of_nonpos_of_nonneg _ (by apply inv_nonneg.mpr; simp)
    simp only [Pi.neg_apply, neg_mul, Left.neg_nonpos_iff]
    apply mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt ((mem_Ioo.mp hx').1)) (le_trans (le_of_lt (mem_Ioo.mp hx').2) hx2)) (pow_nonneg (le_of_lt hx) _)
