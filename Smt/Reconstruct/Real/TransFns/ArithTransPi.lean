/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Implementation of:
https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proof_rules.html#_CPPv4N4cvc58internal6PfRule14ARITH_TRANS_PIE
-/

import Lean
import Qq
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Pi.Bounds

import Smt.Reconstruct.Util

open Lean
open Elab Tactic Meta

open Real

namespace Smt.Reconstruct.Real.TransFns

def expr_pi_upper : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero])
    (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientific [])
    (.lit (.natVal 314159265358979323847)) (mkConst ``Bool.true) (.lit (.natVal 20))

def expr_pi_lower : Expr :=
  mkApp5 (Expr.const ``OfScientific.ofScientific [Level.zero])
    (mkConst ``Rat) (Lean.Expr.const `Rat.instOfScientific [])
    (.lit (.natVal 314159265358979323846)) (mkConst ``Bool.true) (.lit (.natVal 20))

def ratCast_lt_mpr {x y : ℚ} : x < y → (x : ℝ) < (y : ℝ) := ratCast_lt.mpr

def ratOfFloat : Expr → Expr
  | .app (.app (.app (.app (.app a _) _) d) e) f =>
      .app (.app (.app (.app (.app a (mkConst ``Rat)) (mkConst ``Rat.instOfScientific)) d) e) f
  | e => e

def isOfNatNatLit : Expr → Bool
  | .app (.app (.app (.const ``OfNat.ofNat ..) _) _) _ => true
  | _ => false

def ratOfFloatOrNat : Expr → MetaM Expr := fun e =>
  if isOfNatNatLit e then
    mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, e, none]
  else
    pure (ratOfFloat e)

def arithTransPiMetaLt : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``LT.lt #[mkConst ``Rat, none, e, expr_pi_lower]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Mathlib.Meta.NormNum.normNumAt mvarTmp (← Simp.Context.mkDefault) #[]
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_lt_mpr #[val]
    let answer ← mkAppOptM ``lt_trans
      #[mkConst ``Real, none, none, none, none, val', mkConst ``pi_gt_d20]
    return answer

def arithTransPiMetaGt : Expr → MetaM Expr :=
  fun e => do
    let goal ← mkAppOptM ``GT.gt #[mkConst ``Rat, none, e, expr_pi_upper]
    let mvarTmp ← Expr.mvarId! <$> mkFreshExprMVar goal
    let _ ← Mathlib.Meta.NormNum.normNumAt mvarTmp (← Simp.Context.mkDefault) #[]
    let some val ← getExprMVarAssignment? mvarTmp | throwError "unreachable"
    let val' ← mkAppM ``ratCast_lt_mpr #[val]
    let answer ← mkAppOptM ``gt_trans
      #[mkConst ``Real, none, none, none, none, val', mkConst ``pi_lt_d20]
    return answer

def arithTransPiSolve (l u : Expr) : MetaM Expr := do
  let l' ← ratOfFloatOrNat l
  let lt ← inferType l
  let lt' ← inferType l'
  dbg_trace "[arithTransPiSolve]: l = {l}, type = {lt}"
  dbg_trace "[arithTransPiSolve]: l' = {l'}, type = {lt'}"
  let u' ← ratOfFloatOrNat u
  let val₁ ← arithTransPiMetaLt l'
  let val₂ ← arithTransPiMetaGt u'
  mkAppM ``And.intro #[val₁, val₂]

def arithTransPiMeta (mvar : MVarId) : Expr → Expr → Name → MetaM MVarId :=
  fun e₁ e₂ outName => mvar.withContext do
    let answer ← arithTransPiSolve e₁ e₂
    let goal ← inferType answer
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert outName goal answer
    return mvar'

syntax (name := arithTransPi) "arithTransPi" term "," term : tactic

@[tactic arithTransPi] def evalArithTransPi : Tactic := fun stx =>
  withMainContext do
    let e₁ ← elabTerm stx[1] none
    let e₂ ← elabTerm stx[3] none
    let mvar ← getMainGoal
    let fname ← mkFreshId
    let mvar' ← arithTransPiMeta mvar e₁ e₂ fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))

example : 3.1415926535 < Real.pi ∧ Real.pi < 3.1415926536 := by
  arithTransPi 3.1415926535 , 3.1415926536

open Qq in
def arithTransPiTac (mvar : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← mvar.getType
  match t with
  | ~q(Real.pi ≥ $l ∧ Real.pi ≤ $u) =>
    let answer ← arithTransPiSolve l u
    mvar.assign answer
  | _ => throwError "[arithTransPiTac] Unexpected pattern for input metavariable"

end Smt.Reconstruct.Real.TransFns
