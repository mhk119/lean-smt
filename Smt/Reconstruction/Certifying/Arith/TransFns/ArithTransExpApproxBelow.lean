/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule28ARITH_TRANS_EXP_APPROX_BELOWE
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv




#check iteratedDerivWithin_eq_iterate


lemma derivWithin_exp_const_mul (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.exp (c*x)) s x = Real.exp (c*x) * c := by
    have h2 := @differentiableWithinAt_id ℝ _ _ _ (x := x) (s := s)
    have := derivWithin_id x s hxs
    simp [id] at *
    rw [derivWithin_exp (DifferentiableWithinAt.const_mul h2 c) hxs, derivWithin_const_mul hxs]
    simp [this]
    exact h2


theorem iteratedDerivWithin_exp_const_mul (d : Nat) (c : Real) (h : UniqueDiffOn Real s) :
  ∀ x ∈ s, iteratedDerivWithin d (fun x => Real.exp (c*x)) s x = c^d * Real.exp (c*x) := by
  induction' d with d hd
  <;> intro x hx
  <;> have := UniqueDiffOn.uniqueDiffWithinAt h hx
  · simp [iteratedDerivWithin_succ this, iteratedDerivWithin_zero, derivWithin_exp_const_mul this]
  · rw [iteratedDerivWithin_succ this]
    rw [derivWithin_congr hd (hd x hx)]
    rw [derivWithin_const_mul this]
    rw [derivWithin_exp_const_mul this, pow_succ]
    ring
    have hf := DifferentiableWithinAt.const_mul (@differentiableWithinAt_id ℝ _ _ _ (x := x) (s := s)) c
    have h2 := DifferentiableWithinAt.exp (x := x) (s := s) (f := fun x => c*x) (hf := hf)
    simp [h2]

theorem iteratedDerivWithin_exp (d : Nat) (h : UniqueDiffOn Real s):
  ∀ x ∈ s, iteratedDerivWithin d Real.exp s x = Real.exp x := by
  intro x hx
  have := iteratedDerivWithin_exp_const_mul d 1 h x hx
  simpa using this





-- theorem contDiffOn_exp (hx : 0 < x) : ContDiffOn ℝ (n : Nat) Real.exp (Set.Icc 0 x) := by
--   induction' n with n ih
--   · simp [Real.continuousOn_exp]
--   · rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hx)]
--     constructor
--     · simp [DifferentiableOn.exp]
--     · have : ∀ x' ∈ Set.Icc 0 x, derivWithin Real.exp (Set.Icc 0 x) x' = Real.exp x' := by
--         intro x' hx'
--         rw [← iteratedDerivWithin_exp 1 x x' hx hx']
--         simp [iteratedDerivWithin_succ (UniqueDiffOn.uniqueDiffWithinAt (uniqueDiffOn_Icc hx) hx')]
--       rw [contDiffOn_congr this]
--       simp [ih]


theorem arithTransExpApproxBelow₁ (d n : ℕ) (h : d = 2*n + 1) (hx : 0 < x) :
    Real.exp x ≥ taylorWithinEval Real.exp d (Set.Icc 0 x) 0 x := by
  have := ContDiffOn.exp (f := id) (s := Set.Icc 0 x) (hf := contDiffOn_id) (n := d)
  have h2 := DifferentiableOn.exp (f := id) (s := Set.Ioo 0 x) (hc := differentiableOn_id)
  have h3 := fun x' hx' => (iteratedDerivWithin_exp d (by sorry)) x' ((@Set.Ioo_subset_Icc_self _ _ 0 x) hx')
  have ⟨x', hx', Hx'⟩ := @taylor_mean_remainder_lagrange Real.exp x 0 d hx this
                        (by rw [differentiableOn_congr h3]; exact h2)
  apply sub_nonneg.mp
  rw [Hx']
  apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
  apply mul_nonneg
    (by rw [iteratedDerivWithin_exp _ (by sorry) _ (by sorry)]; exact le_of_lt (Real.exp_pos x')) (by simp [le_of_lt hx])


theorem iteratedDerivWithin_congr {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} {s : Set 𝕜} (hs : Set.EqOn f₁ f s) (hx : f₁ x = f x) (hxs : UniqueDiffOn 𝕜 s) (hx2 : x ∈ s) : iteratedDerivWithin n f₁ s x = iteratedDerivWithin n f s x := by
  revert x
  induction' n with n hn
  <;> intro x hx hx2
  · simp [hx]
  · simp only [iteratedDerivWithin_succ (UniqueDiffOn.uniqueDiffWithinAt hxs hx2)]
    simp only [Set.EqOn] at hs
    rw [derivWithin_congr (by simp [Set.EqOn]; intro y hy; exact hn (hs hy) hy) (hn hx hx2)]


example (a b : Real) (ha : a < b) (hx: x ∈ Set.Ioo a b) : x ∈ Set.Icc a b := by
  exact Set.mem_Icc_of_Ioo hx

theorem arithTransExpApproxBelow₂' (d n : ℕ) (h : d = 2*n + 1) (hx : 0 < x) :
    Real.exp (-x) ≥ taylorWithinEval (fun x => Real.exp (-x)) d (Set.Icc 0 x) 0 x := by
    have ⟨x', hx', Hx'⟩ := @taylor_mean_remainder_lagrange (fun x => Real.exp (-x)) x 0 d (by linarith) (by sorry) (by sorry)
    apply sub_nonneg.mp
    rw [Hx']
    apply mul_nonneg _ (by apply inv_nonneg.mpr; simp)
    rw [iteratedDerivWithin_congr _ _ (uniqueDiffOn_Icc hx) (Set.mem_Icc_of_Ioo hx')]
    apply mul_nonneg
      (by rw [@iteratedDerivWithin_exp_const_mul _ _ (-1) (by sorry) _ (by sorry)]
          simp [le_of_lt _, Real.exp_pos, show d+1 = 2*(n+1) by linarith])
      (by simp [le_of_lt hx])
    · simp [Set.EqOn]
    · simp


#check Polynomial.eval₂_congr
#check iteratedDerivWithin_exp_const_mul
#check Finset.sum_congr

lemma taylorCoeffWithin_exp (d n : ℕ) (h : d = 2*n + 1) (hx : x < 0) :
  taylorCoeffWithin Real.exp d (Set.Icc (-|x|) 0) (-|x|) = -taylorCoeffWithin (fun x => Real.exp (-x)) d (Set.Icc 0 |x|) |x| := by
  simp only [taylorCoeffWithin]
  rw [← iteratedDerivWithin_congr (f := fun i => Real.exp (-i)) (f₁ := fun i => Real.exp (-1*i)) (by sorry) (by sorry) (by sorry) (by sorry)]
  rw [iteratedDerivWithin_exp_const_mul d]
  rw [iteratedDerivWithin_exp d (by sorry)]
  rw [h]
  norm_num
  all_goals sorry

example (x : Real) (hx: 0 ≤ x) : 0 ∈ Set.Icc 0 x := by
  exact Set.left_mem_Icc.mpr hx

lemma taylorCoeffWithin_exp' (d n : ℕ) (hx : x < 0) :
  taylorCoeffWithin Real.exp d (Set.Icc (-|x|) 0) 0 = (-1)^d * taylorCoeffWithin (fun x => Real.exp (-x)) d (Set.Icc 0 |x|) 0 := by
  simp only [taylorCoeffWithin]
  rw [← iteratedDerivWithin_congr (f := fun i => Real.exp (-i)) (f₁ := fun i => Real.exp (-1*i)) (by sorry) (by sorry) (by sorry) (Set.left_mem_Icc.mpr (abs_nonneg x))]
  rw [iteratedDerivWithin_exp_const_mul d _ (by sorry) _ (Set.left_mem_Icc.mpr (abs_nonneg x))]
  rw [iteratedDerivWithin_exp d (by sorry) _ (by sorry)]
  norm_num
  rw [mul_comm, mul_assoc, ← pow_add, ← mul_two]
  simp


#check Polynomial.X

#check PolynomialModule.eval ((-1 : Real)) (Polynomial.X ^ (3 : Nat) • (10 : Real): PolynomialModule Real Real)


-- lemma Polynomial.eval_neg_x  (p : Polynomial ℝ) (x : ℝ) (C : PolynomialModule Real Real) (d : Nat) :
--   ((PolynomialModule.eval (-x)) (Polynomial.X ^ d • C) : Real) = ((PolynomialModule.eval x) (Polynomial.X ^ d • C) : Real) := by
--   simp [eval, eval₂]
--   apply Finset.sum_congr
--   · sorry
--   · intro y hy
--     simp
--     sorry


#check PolynomialModule.eval

lemma taylorWithin_exp (d n : ℕ) (h : d = 2*n + 1) (hx : x < 0) :
  taylorWithinEval Real.exp d (Set.Icc (-|x|) 0) 0 (-|x|) =
  taylorWithinEval (fun x => Real.exp (-x)) d (Set.Icc 0 |x|) 0 |x| := by
  unfold taylorWithinEval
  unfold taylorWithin
  rw [Finset.sum_congr rfl
      (by intro d _; rw [taylorCoeffWithin_exp' d n hx])]
  simp
  apply Finset.sum_congr rfl
  intro d _
  set C := (PolynomialModule.lsingle ℝ 0) ((-1) ^ d * taylorCoeffWithin (fun x => Real.exp (-x)) d (Set.Icc 0 |x|) 0)
  set C' := (PolynomialModule.lsingle ℝ 0) (taylorCoeffWithin (fun x => Real.exp (-x)) d (Set.Icc 0 |x|) 0)
  simp only [PolynomialModule.eval_smul, Polynomial.eval_pow, Polynomial.eval_X]
  simp [← mul_pow, ← mul_assoc]



theorem arithTransExpApproxBelow₂ (d n : ℕ) (h : d = 2*n + 1) (hx : x < 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d (Set.Icc x 0) 0 x := by
  have : x = -|x| := sorry
  rw [this]
  have H := arithTransExpApproxBelow₂' d n h (show 0 < |x| by linarith)
  apply Eq.trans_le _ H
  rw [taylorWithin_exp d n h hx]










/- example (x : ℝ) : x < 0 → -x > 0 := by intro h; library_search -/


/- #check Convex -/
/- example : StrictConvexOn ℝ  (Set.Icc 1 2) Real.exp := by -/
/-   simp [StrictConvexOn] -/
/-   apply And.intro -/
/-   · admit -/
/-   · admit -/
