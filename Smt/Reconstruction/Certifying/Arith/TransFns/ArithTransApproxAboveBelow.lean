/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

/-
A genral framework for lower-bounding and upper-boudning functions for
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule28ARITH_TRANS_EXP_APPROX_BELOWE
and some sine rules.
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Nat

open Set

theorem iteratedDerivWithin_congr {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f₁ : 𝕜 → F} {x : 𝕜} {s : Set 𝕜} (hs : Set.EqOn f₁ f s) (hx : f₁ x = f x) (hxs : UniqueDiffOn 𝕜 s) (hx2 : x ∈ s) : iteratedDerivWithin n f₁ s x = iteratedDerivWithin n f s x := by
  revert x
  induction' n with n hn
  <;> intro x hx hx2
  · simp [hx]
  · simp only [iteratedDerivWithin_succ (UniqueDiffOn.uniqueDiffWithinAt hxs hx2)]
    simp only [Set.EqOn] at hs
    rw [derivWithin_congr (by simp [Set.EqOn]; intro y hy; exact hn (hs hy) hy) (hn hx hx2)]


theorem deriv_comp_mul {f : Real → Real} (hd : Differentiable Real f) :
  ∀ x, deriv (fun x => f (c*x)) x = c * deriv f (c*x) := by
  intro x
  rw [show (fun x => f (c*x)) = f ∘ (fun x => c*x) by rfl]
  rw [deriv.comp _ (Differentiable.differentiableAt hd) (by apply DifferentiableAt.const_mul (differentiableAt_id'))]
  rw [deriv_const_mul _ (differentiableAt_id'), mul_comm]
  simp


theorem iteratedDeriv_const_mul {f : ℝ → ℝ } (d : Nat) (c : Real) (hf : ContDiff Real ⊤ f):
  ∀ x, iteratedDeriv d (fun x => f (c*x)) x = c^d * (iteratedDeriv d f (c*x)) := by
  induction' d with d ih
  · simp
  · intro x
    rw [iteratedDeriv_succ]
    rw [congrArg deriv (funext ih)]
    rw [deriv_const_mul, deriv_comp_mul, ← iteratedDeriv_succ, pow_succ', ← mul_assoc]
    apply ContDiff.differentiable_iteratedDeriv d hf (Ne.lt_top (ENat.top_ne_coe d).symm)
    apply Differentiable.differentiableAt
    rw [show (fun x => iteratedDeriv d f (c * x)) = ((iteratedDeriv d f) ∘ (fun x => c*x)) by rfl]
    apply Differentiable.comp (ContDiff.differentiable_iteratedDeriv d ((contDiff_top.mp hf) (d+1)) (by norm_cast; simp))
    apply Differentiable.const_mul (differentiable_id)

lemma taylorCoeffWithin_neg (d n : ℕ) (hf : ContDiff Real ⊤ f):
  taylorCoeffWithin f d Set.univ x₀ = (-1 : Real)^d * taylorCoeffWithin (fun x => f (-x)) d Set.univ (-x₀) := by
  simp only [taylorCoeffWithin]
  rw [← iteratedDerivWithin_congr (f := fun i => f (-i)) (f₁ := fun i => f (-1*i)) (by simp [Set.eqOn_refl]) (by simp [Set.eqOn_refl]) uniqueDiffOn_univ (mem_univ _)]
  rw [iteratedDerivWithin_univ, iteratedDerivWithin_univ, iteratedDeriv_const_mul d _ hf]
  simp only [ mul_neg, neg_mul, one_mul, neg_neg]
  rw [mul_comm, smul_eq_mul, smul_eq_mul, mul_assoc]; congr 1
  rw [mul_comm, ← mul_assoc, ← pow_add, ← two_mul, Even.neg_one_pow (by simp), one_mul]


theorem taylorWithinEval_neg {f : Real → Real} (hf : ContDiff Real ⊤ f):
  taylorWithinEval f n Set.univ x₀ x =
  taylorWithinEval (fun x => f (-x)) n Set.univ (-x₀) (-x) := by
  unfold taylorWithinEval
  unfold taylorWithin
  rw [Finset.sum_congr rfl
      (by intro d _; rw [taylorCoeffWithin_neg d n hf])]
  simp
  apply Finset.sum_congr rfl
  intro d _
  simp only [PolynomialModule.eval_smul, Polynomial.eval_pow, Polynomial.eval_X]
  simp [← mul_pow, ← mul_assoc]
  apply Or.inl; ring

theorem derivWithin_eq_deriv {f : Real → Real} (hf : ContDiff Real ⊤ f) (hs : UniqueDiffWithinAt Real s x):
  derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv]
  rw [fderivWithin_eq_fderiv hs (ContDiffAt.differentiableAt (ContDiff.contDiffAt hf) (by simp))]


theorem iteratedDerivWithin_eq_iteratedDeriv {f : Real → Real} (hf : ContDiff Real ⊤ f) (hs : UniqueDiffOn Real s):
  ∀ x ∈ s, iteratedDerivWithin d f s x = iteratedDeriv d f x := by
  induction' d with d hd
  · simp
  · intro x hx
    rw [iteratedDerivWithin_succ (UniqueDiffOn.uniqueDiffWithinAt hs hx), iteratedDeriv_succ, derivWithin, deriv]
    rw [fderivWithin_congr hd (hd x hx)]
    rw [fderivWithin_eq_fderiv (UniqueDiffOn.uniqueDiffWithinAt hs hx)]
    apply Differentiable.differentiableAt (ContDiff.differentiable_iteratedDeriv d ((contDiff_top.mp hf) (d + 1)) (by norm_cast; simp))

-- This should be generalized
theorem taylorCoeffWithin_eq {f : Real → Real} (s : Set Real) (hx : x₀ ∈ s) (hs : UniqueDiffOn ℝ s) (hf : ContDiff Real ⊤ f):
  (taylorCoeffWithin f d s x₀) = (taylorCoeffWithin f d Set.univ x₀) := by
  simp only [taylorCoeffWithin]
  rw [iteratedDerivWithin_eq_iteratedDeriv hf hs _ hx, iteratedDerivWithin_univ]

-- This should be generalized
theorem taylorWithinEval_eq {f : Real → Real} (s : Set Real) (hs : x₀ ∈ s) (hs1 : UniqueDiffOn ℝ s) (hf : ContDiff Real ⊤ f) :
  (taylorWithinEval f d s x₀) = (taylorWithinEval f d Set.univ x₀) := by
  ext x
  simp only [taylorWithinEval, taylorWithin, taylorCoeffWithin_eq s hs hs1 hf]



#check taylor_mean_remainder_lagrange
theorem taylor_mean_remainder_lagrange₁ {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x < x₀)
  (hf : ContDiff ℝ ⊤ f)
  :
  ∃ (x' : ℝ) (_ : x' ∈ Ioo x x₀), f x - taylorWithinEval f n (Icc x x₀) x₀ x =
    iteratedDerivWithin (n + 1) f (Icc x x₀) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have H1 := (show (f ∘ (fun x => -x)) = (fun p => f (-p)) by rfl) ▸ ContDiff.comp hf contDiff_neg
  have H2 : DifferentiableOn ℝ (iteratedDerivWithin n (fun x => f (-x)) (Icc (-x₀) (-x))) (Ioo (-x₀) (-x)) := by
    apply DifferentiableOn.mono _ Set.Ioo_subset_Icc_self
    apply ContDiffOn.differentiableOn_iteratedDerivWithin (n := n + 1) _ (by norm_cast; simp) (uniqueDiffOn_Icc (neg_lt_neg hx))
    apply ContDiff.contDiffOn ((contDiff_top.mp H1) _)
  have ⟨x' , hx', H⟩:= taylor_mean_remainder_lagrange (f := fun x => f (-x)) (n := n) (neg_lt_neg hx) (ContDiff.contDiffOn ((contDiff_top.mp H1) n)) H2
  have hx'' : -x' ∈ Ioo x x₀ := by
    simp at *
    apply And.intro
    <;> apply neg_lt_neg_iff.mp
    <;> simp [hx']
  use -x'; use hx''
  rw [neg_neg, taylorWithinEval_eq _ (by simp [le_of_lt hx]) (uniqueDiffOn_Icc (by simp [hx])) H1] at H
  rw [taylorWithinEval_neg H1, ←taylorWithinEval_eq (Icc x x₀) (by simp [le_of_lt hx]) (uniqueDiffOn_Icc hx) (by simp [hf])] at H
  simp only [neg_neg, sub_neg_eq_add] at H
  rw [H, iteratedDerivWithin_eq_iteratedDeriv hf (uniqueDiffOn_Icc (by simp [hx])) _ (Set.Ioo_subset_Icc_self hx''), iteratedDerivWithin_eq_iteratedDeriv H1 (uniqueDiffOn_Icc (by simp [hx])) _ (Set.Ioo_subset_Icc_self hx')]
  rw [show (fun x => f (-x)) = (fun x => f (-1 * x)) by simp]
  rw [iteratedDeriv_const_mul _ _ hf, mul_rotate, mul_assoc, ←mul_pow, add_comm (-x) x₀]
  simp [sub_eq_add_neg]
