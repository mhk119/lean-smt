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

namespace Smt.Reconstruct.Real.TransFns

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

end Smt.Reconstruct.Real.TransFns
