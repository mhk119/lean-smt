/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Recognizers
import Smt.Reconstruct.Real.Polynorm

namespace Smt.Reconstruct.Real

open Lean Qq

abbrev PolyM := StateT (Array Q(Int) × Array Q(Real)) MetaM

def getIntIndex (e : Q(Int)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e, rs)
    return size

def getRealIndex (e : Q(Real)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := rs.findIdx? (· == e) then
    return i
  else
    let size := rs.size
    set (is, rs.push e)
    return size

partial def reifyRealVal (e : Q(Real)) : PolyM Q(PolyNorm.RealValExpr) := do
  if let some n := e.natLitOf? q(Real) then
    return q(.val (OfNat.ofNat $n))
  else if let some e := e.negOf? q(Real) then
    return q(.neg $(← reifyRealVal e))
  else if let some (x, y) := e.hAddOf? q(Real) q(Real) then
    return q(.add $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hSubOf? q(Real) q(Real) then
    return q(.sub $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hMulOf? q(Real) q(Real) then
    return q(.mul $(← reifyRealVal x) $(← reifyRealVal y))
  else if let some (x, y) := e.hDivOf? q(Real) q(Real) then
    return q(.div $(← reifyRealVal x) $(← reifyRealVal y))
  else
    throwError "[poly_norm] expected a rational number, got {e}"

partial def reifyInt (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  if let some e := e.natLitOf? q(Int) then
    return q(.val (OfNat.ofNat $e))
  else if let some e := e.negOf? q(Int) then
    return q(.neg $(← reifyInt e))
  else if let some (x, y) := e.hAddOf? q(Int) q(Int) then
    return q(.add $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hSubOf? q(Int) q(Int) then
    return q(.sub $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hMulOf? q(Int) q(Int) then
    return q(.mul $(← reifyInt x) $(← reifyInt y))
  else
    let v : Nat ← getIntIndex e
    return q(.var $v)

partial def reifyReal (e : Q(Real)) : PolyM Q(PolyNorm.RealExpr) := do
  if let some e := e.natLitOf? q(Real) then
    return q(.val (OfNat.ofNat $e))
  else if let some e := e.negOf? q(Real) then
    return q(.neg $(← reifyReal e))
  else if let some (x, y) := e.hAddOf? q(Real) q(Real) then
    return q(.add $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hSubOf? q(Real) q(Real) then
    return q(.sub $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hMulOf? q(Real) q(Real) then
    return q(.mul $(← reifyReal x) $(← reifyReal y))
  else if let some (x, y) := e.hDivOf? q(Real) q(Real) then
    return q(.divConst $(← reifyReal x) $(← reifyRealVal y))
  else if let some e := e.intCastOf? q(Real) then
    return q(.cast $(← reifyInt e))
  else
    let v : Nat ← getRealIndex e
    return q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyReal l).run (#[], #[])
  let (r, (is, rs)) ← (reifyReal r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let rctx : Q(PolyNorm.RealContext) ← if h : 0 < rs.size
    then do let rs : Q(RArray Real) ← (RArray.ofArray rs h).toExpr q(Real) id; pure q(«$rs».get)
    else pure q(fun _ => 0)
  let h : Q(«$l».toPoly = «$r».toPoly) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPoly)
  mv.assign q(@PolyNorm.RealExpr.eval_eq_from_toPoly_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyReal l).run (#[], #[])
  let (r, (is, rs)) ← (reifyReal r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let rctx : Q(PolyNorm.RealContext) ← if h : 0 < rs.size
    then do let rs : Q(RArray Real) ← (RArray.ofArray rs h).toExpr q(Real) id; pure q(«$rs».get)
    else pure q(fun _ => 0)
  let h ← nativeDecide q(«$l».toPoly = «$r».toPoly)
  mv.assign q(@PolyNorm.RealExpr.eval_eq_from_toPoly_eq $ictx $rctx $l $r $h)
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← match (← getEnv).asyncPrefix? with
      | none          => Lean.mkAuxName baseName 1
      | some declName => Lean.mkAuxName (declName ++ baseName) 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  if let some (_, mv) ← normNumAt mv (← Meta.Simp.mkContext) #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

open Mathlib.Meta.NormNum in
def normNumAbs (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let simpTheorems ← simpTheorems.addDeclToUnfold `abs
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  if let some (_, mv) ← Mathlib.Meta.NormNum.normNumAt mv ctx #[] true true then
    throwError "[norm_num]: could not prove {← mv.getType}"

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Real.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Real.Tactic

example (x y z : Real) : 1 * (x + y) * z / 4 = 1 / (2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * (↑x + ↑y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm

example (x y : Int) (z : Real) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  native_poly_norm
