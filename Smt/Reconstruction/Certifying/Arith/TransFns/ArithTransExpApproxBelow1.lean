import Smt.Reconstruction.Certifying.Arith.TransFns.ArithTransApproxAboveBelow
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


#check sub_nonneg
open Set Real

example (a b c : Real) (ha : a -b ≥ c) : a ≥ c+b := by
    exact le_sub_iff_add_le.mp ha

theorem iteratedDeriv_exp (n : Nat) : iteratedDeriv n exp = exp := by
    induction' n with n hn
    · simp
    · simp [iteratedDeriv_succ, hn]


-- can definitely be shortened. same proof below
theorem arithTransExpApproxBelow₁ (d n : ℕ) (h : d = 2*n + 1) (hx : 0 < x) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have h2 : DifferentiableOn ℝ (iteratedDerivWithin d rexp (Icc 0 x)) (Ioo 0 x) := by
        apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
        apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := d + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc hx)
        apply ContDiff.contDiffOn ((contDiff_top.mp contDiff_exp) _)
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange hx (ContDiff.contDiffOn (s := Icc 0 x) (n := d) contDiff_exp) h2
    rw [taylorWithinEval_eq _ (left_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x')) (by simp [le_of_lt hx])


-- see the last line. this probably holds for any function.
theorem arithTransExpApproxBelow₂ (d n : ℕ) (h : d = 2*n + 1) (hx : x < 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    have ⟨x', hx', H⟩ := taylor_mean_remainder_lagrange₁ hx contDiff_exp (n := d)
    rw [taylorWithinEval_eq _ (right_mem_Icc.mpr (le_of_lt hx)) (uniqueDiffOn_Icc hx) contDiff_exp] at H
    rw [ge_iff_le, ←sub_nonneg, H]
    rw [iteratedDerivWithin_eq_iteratedDeriv contDiff_exp (uniqueDiffOn_Icc hx) _ (Ioo_subset_Icc_self hx'), iteratedDeriv_exp]
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    apply mul_nonneg (le_of_lt (Real.exp_pos x'))
    apply Even.pow_nonneg; rw [h, show 2*n + 1 + 1 = 2*(n+1) by ring]; simp
