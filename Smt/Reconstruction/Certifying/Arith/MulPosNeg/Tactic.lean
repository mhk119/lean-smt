/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Smt.Reconstruction.Certifying.Arith.MulPosNeg.Lemmas

import Mathlib.Data.Rat.Order
import Mathlib.Data.Int.Order.Basic

import Lean

namespace Smt.Reconstruction.Certifying

open Lean hiding Rat
open Elab.Tactic Expr Meta

syntax (name := arithMulPos) "arithMulPos" term "," term : tactic
@[tactic arithMulPos] def evalArithMulPos : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← Meta.inferType h₁
    let thmName ← getThmName t₁
    let proof : Expr ← mkAppM thmName #[h₁, h₂]
    closeMainGoal proof
where getThmName : Expr → TacticM Name
        | app (app (app (app (app (const nm ..) ..) ..) ..) ..) _ => matchNameThm nm
        | app (app (app (app (const nm ..) ..) ..) ..) _ => matchNameThm nm
        | _ => throwError "[arithMulPos]: structure not supported"
      matchNameThm : Name → TacticM Name
        | ``LE.le => pure ``arith_mul_pos_le
        | ``LT.lt => pure ``arith_mul_pos_lt
        | ``GT.gt => pure ``arith_mul_pos_gt
        | ``GE.ge => pure ``arith_mul_pos_ge
        | _ => throwError "[arithMulPos]: invalid comparator"

syntax (name := arithMulNeg) "arithMulNeg" term "," term : tactic
@[tactic arithMulNeg] def evalArithMulNeg : Tactic := fun stx =>
  withMainContext do
    let h₁ ← elabTerm stx[1] none
    let h₂ ← elabTerm stx[3] none
    let t₁ ← Meta.inferType h₁
    let thmName ← getThmName t₁
    let proof : Expr ← mkAppM thmName #[h₁, h₂]
    closeMainGoal proof
where getThmName : Expr → TacticM Name
        | app (app (app (app (app (const nm ..) ..) ..) ..) ..) _ => matchNameThm nm
        | app (app (app (app (const nm ..) ..) ..) ..) _ => matchNameThm nm
        | _ => throwError "[arithMulNeg]: structure not supported"
      matchNameThm : Name → TacticM Name
        | ``LE.le => pure ``arith_mul_neg_le
        | ``LT.lt => pure ``arith_mul_neg_lt
        | ``GT.gt => pure ``arith_mul_neg_gt
        | ``GE.ge => pure ``arith_mul_neg_ge
        | _ => throwError "[arithMulNeg]: invalid comparator"

end Smt.Reconstruction.Certifying
