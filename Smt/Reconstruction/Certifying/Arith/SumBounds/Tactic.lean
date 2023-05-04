/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas
import Smt.Reconstruction.Certifying.Arith.SumBounds.Instances

open Lean hiding Rat
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying

def combineBounds : Expr → Expr → TacticM Expr := fun h₁ h₂ =>
  withMainContext do
    let t₁ ← inferType h₁
    let t₂ ← inferType h₂
    let thmName : Name ←
      match ← getOp t₁, ← getOp t₂ with
      | ``LT.lt , ``LT.lt => pure ``sumBounds₁
      | ``LT.lt , ``LE.le => pure ``sumBounds₂
      | ``LT.lt , ``Eq    => pure ``sumBounds₃
      | ``LE.le , ``LT.lt => pure ``sumBounds₄
      | ``LE.le , ``LE.le => pure ``sumBounds₅
      | ``LE.le , ``Eq    => pure ``sumBounds₆ 
      | ``Eq    , ``LT.lt => pure ``sumBounds₇
      | ``Eq    , ``LE.le => pure ``sumBounds₈
      | ``Eq    , ``Eq    => pure ``sumBounds₉
      | _      , _      => throwError "[sumBounds] invalid operation"
    mkAppM thmName #[h₁, h₂]
where
  getOp : Expr → TacticM Name
    | app (app (app (app (Expr.const nm ..) ..) ..) ..) .. => pure nm
    | app (app (app (Expr.const nm ..) ..) ..) .. => pure nm
    | _ => throwError "[sumBounds] invalid parameter"

syntax (name := sumBounds) "sumBounds" "[" term,* "]" : tactic

def parseSumBounds : Syntax → TacticM (List Expr)
  | `(tactic| sumBounds [$[$hs],*]) =>
    hs.toList.mapM (λ stx => elabTerm stx.raw none)
  | _ => throwError "[sumBounds]: expects a list of premisses"

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    let (h, hs) ←
      match ← parseSumBounds stx with
      | h::hs => pure (h, hs)
      | [] => throwError "[sumBounds]: empty list of premisses"
    go h hs
where
  go : Expr → List Expr → TacticM Unit
    | acc, []    => closeMainGoal acc
    | acc, e::es => do
      let acc' ← combineBounds acc e
      go acc' es

end Smt.Reconstruction.Certifying
