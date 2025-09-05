/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Definition of a computable version of the taylor polynomial of `exp` to be used in the reconstruction.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxBelow

import Smt.Reconstruct.Real.TransFns.ArithTransExpApproxBelow
import Smt.Reconstruct.Real.TransFns.Utils

namespace Smt.Reconstruct.Real.TransFns

def expTaylor' (i : Nat) (x : Rat) : Rat :=
  match i with
  | 0 => 1
  | i + 1 => expTaylor' i x + (x ^ (i + 1)) / (i + 1).factorial

@[simp]
noncomputable def expTaylor (i : Nat) (x : Real) : Real :=
  match i with
  | 0 => 1
  | i + 1 => expTaylor i x + (x ^ (i + 1)) / (i + 1).factorial

theorem expEmbedding (d : Nat) (x : Real) : taylorWithinEval Real.exp d Set.univ 0 x = expTaylor d x := by
  rw [taylor_exp_eq]
  induction d
  next => simp
  next d IH =>
    simp
    rw [<- IH, Finset.sum_range_succ (n := d + 1)]

noncomputable def sinTaylor (i : Nat) (x : Real) : Real :=
  match i with
  | 0 => 0
  | i + 1 =>
    let m := match (i + 1) % 4 with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | _ => -1
    m * x ^ (i + 1) / (i + 1).factorial + sinTaylor i x

def f : Nat → Real
| 0 => 0
| 1 => 1
| 2 => 0
| _ => -1

/- def sinTaylor' (i : Nat) (x : Rat) : Rat := -/
/-   match i with -/
/-   | 0 => 0 -/
/-   | i + 1 => -/
/-     let m := f ((i + 1) % 4) -/
/-     m * x ^ (i + 1) / (i + 1).factorial + sinTaylor' i x -/

lemma taylor_sin_eq (d : ℕ) (x : ℝ) :
    taylorWithinEval Real.sin d Set.univ 0 x =
      ∑ i ∈ Finset.range (d + 1), f (i % 4) * x^i / Nat.factorial i := by
  rw [taylor_within_apply]
  congr
  ext k
  obtain ⟨h1, _⟩ := iteratedDeriv_sin_cos k
  rw [iteratedDerivWithin_eq_iteratedDeriv (f := Real.sin) (d := k) (s := Set.univ)]
  · simp
    if hk0: k % 4 = 0 then
      rw [hk0] at h1
      simp at h1
      rw [hk0, f, h1]
      simp
    else if hk1 : k % 4 = 1 then
      rw [hk1] at h1
      simp at h1
      rw [hk1, f, h1]
      field_simp
    else if hk2 : k % 4 = 2 then
      rw [hk2] at h1
      simp at h1
      rw [hk2, f, h1]
      field_simp
    else
      have hk3 : k % 4 = 3 := by omega
      rw [hk3] at h1
      simp at h1
      rw [hk3, f, h1]
      · field_simp
      · decide
      · decide
      · decide
  · exact Real.contDiff_sin
  · exact uniqueDiffOn_univ
  · exact trivial

theorem sinEmbedding (d : Nat) (x : Real) : taylorWithinEval Real.sin d Set.univ 0 x = sinTaylor d x := by
  rw [taylor_sin_eq]
  induction d
  next => simp [f, sinTaylor]
  next d' IH =>
    simp [sinTaylor, f]
    rw [<- IH, Finset.sum_range_succ (n := d' + 1)]
    simp [f]
    rw [add_comm]

def sinTaylor'' (i : Nat) (x : Rat) : String :=
  match i with
  | 0 => "0"
  | i + 1 =>
    let m := match (i + 1) % 4 with
    | 0 => "0"
    | 1 => "1"
    | 2 => "0"
    | _ => "(-1)"
    let s := if m != "0" then
      m ++ " * " ++ (toString x) ++ " ^ " ++ (toString (i + 1)) ++ " / " ++ (toString (i + 1).factorial) ++ "! + "
      else ""
    s ++ sinTaylor'' i x

/- #eval toString ((3 : Rat)/2) -/


/- def lb : Rat := 3.0 -/
/- def ub : Rat := 0.5 -/
/- def d := 13 -/

/- #eval sinTaylor' d lb - lb ^ (d + 1) / (d + 1).factorial -/
/- #eval sinTaylor' d ub - ub ^ (d + 1) / (d + 1).factorial -/


end Smt.Reconstruct.Real.TransFns
