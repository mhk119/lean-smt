/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule32ARITH_TRANS_EXP_APPROX_ABOVE_NEGE
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

-- import Smt.Reconstruction.Certifying.Arith.TransFns.ArithTransExpApproxBelow



theorem expApproxAbove (d k : Nat) (hd : d = 2*k) :
  Real.exp x ≤ taylorWithinEval Real.exp d Set.univ 0 x := by
  sorry

example (a b c d : Real) (ha : a/b ≤ c/b) (hb: 0 < b) : 1-(1-c) = c := by
  exact sub_sub_self 1 c

example (a b c d : Real) (ha : a=d) (hb : c < d):  c < a:= by
  exact Eq.trans_gt (id ha.symm) hb


#check ConvexOn.secant_mono_aux2
#reduce LinearOrderedField Real

example (a b c : Real) (h : (0 ≤ t)) : a/b*c = a*c/b := by
  exact div_mul_eq_mul_div a b c

theorem le_of_ConvexOn (f : ℝ → ℝ) (hf : ConvexOn Real Set.univ f) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxz : x < z):
  f (t*x + (1-t)*z) ≤ t*(f x) + (1-t)*(f z) := by
  cases' eq_or_gt_of_le ht0 with ht0 ht0
  · simp [ht0]
  · cases' eq_or_gt_of_le ht1 with ht1 ht1
    · simp [← ht1]
    · have := ConvexOn.secant_mono_aux2 hf (Set.mem_univ x) (Set.mem_univ z)
              (Eq.trans_lt
                (by ring)
                ((add_lt_add_iff_left _).mpr ((mul_lt_mul_left (by linarith)).mpr hxz))) (show t*x + (1-t)*z < z by
                  apply Eq.trans_gt
                        (by ring)
                        ((add_lt_add_iff_right _).mpr ((mul_lt_mul_left (by linarith)).mpr hxz)))
      rw [show t*x + (1-t)*z -x = (1-t)*(z-x) by linarith, div_mul_eq_div_div] at this
      rw [div_le_div_right (by linarith), div_le_iff' (by linarith)] at this
      linarith


example (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) :1-(1-a) = a:= by
  exact sub_sub_self 1 a


theorem arithTransExpApproxAboveNeg (d k : Nat) (hd : d = 2*k) (l u t : ℝ) (ht : l ≤ t ∧ t ≤ u) :
  let p: ℝ → ℝ := taylorWithinEval Real.exp d Set.univ 0
  Real.exp t ≤ ((p l - p u) / (l - u)) * (t - l) + p l := by
  intro p
  have hp : ∀ x, p x = taylorWithinEval Real.exp d Set.univ 0 x := by simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub, mul_comm_div]
  have H1 := fun j => (hp u).symm ▸ @expApproxAbove j d k hd
  cases' (lt_or_eq_of_le (le_trans ht.1 ht.2)) with hlu hlu
  · set C := (t-l)/(u-l) with hc
    rw [sub_mul, sub_add_eq_add_sub, ← mul_one (p l), mul_assoc, add_sub_assoc, ←mul_sub (p l), one_mul]
    have HC : 0 ≤ C ∧ C ≤ 1 := by
      rw [hc]
      simp only [true_and, div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr (le_of_lt hlu))]
      apply div_le_one_of_le (by linarith) (by linarith)
    have H3 := le_of_ConvexOn Real.exp convexOn_exp (show 0 ≤ 1 - C by linarith) (by linarith) hlu
    have ht : (1-C) * l + (1-(1-C)) * u = t := by
      field_simp [show u -l ≠ 0 by linarith]
      ring
    rw [ht, sub_sub_self, add_comm] at H3
    rw [mul_comm, mul_comm (p l)]
    apply le_trans H3
    apply add_le_add (mul_le_mul_of_nonneg_left (H1 u) HC.1) (mul_le_mul_of_nonneg_left (H1 l) (by linarith))
  · simp [hlu, hp, (show t = u by linarith), H1]
