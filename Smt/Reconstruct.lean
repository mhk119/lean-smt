/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5
import Qq
import Smt.Reconstruct.BitVec
import Smt.Reconstruct.Builtin
import Smt.Reconstruct.Int
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Quant
--import Smt.Reconstruct.Rat
import Smt.Reconstruct.Real
import Smt.Reconstruct.UF

namespace Smt

open Lean

namespace Reconstruct

def sortRcons := [
  (Builtin.reconstructBuiltinSort, ``Builtin.reconstructBuiltinSort),
  (Prop.reconstructPropSort, ``Prop.reconstructPropSort),
  (UF.reconstructUS, ``UF.reconstructUS),
  (Int.reconstructIntSort, ``Int.reconstructIntSort),
  --(Rat.reconstructRatSort,``Rat.reconstructRatSort),
  (Real.reconstructRealSort, ``Real.reconstructRealSort),
  (BitVec.reconstructBitVecSort, ``BitVec.reconstructBitVecSort)
]

def termRcons := [
  (Builtin.reconstructBuiltin, ``Builtin.reconstructBuiltin),
  (Prop.reconstructProp, ``Prop.reconstructProp),
  (UF.reconstructUF, ``UF.reconstructUF),
  (Quant.reconstructQuant, ``Quant.reconstructQuant),
  (Int.reconstructInt, ``Int.reconstructInt),
  --(Rat.reconstructRat, ``Rat.reconstructRat),
  (Real.reconstructReal, ``Real.reconstructReal),
  (BitVec.reconstructBitVec, ``BitVec.reconstructBitVec)
]

def proofRcons := [
  (Builtin.reconstructBuiltinProof, ``Builtin.reconstructBuiltinProof),
  (Prop.reconstructPropProof, ``Prop.reconstructPropProof),
  (UF.reconstructUFProof, ``UF.reconstructUFProof),
  (Quant.reconstructQuantProof, ``Quant.reconstructQuantProof),
  (Int.reconstructIntProof, ``Int.reconstructIntProof),
  --(Rat.reconstructRatProof, ``Rat.reconstructRatProof),
  (Real.reconstructRealProof, ``Real.reconstructRealProof),
  (BitVec.reconstructBitVecProof, ``BitVec.reconstructBitVecProof)
]

@[export smt_reconstruct_sort]
def reconstructSortImpl (s : cvc5.Sort) : ReconstructM Expr := do
  let rs := sortRcons
  go rs s
where
  go (rs : List (SortReconstructor × Name)) (s : cvc5.Sort) : ReconstructM Expr := do
    for (r, n) in rs do
      if let some e ← r s then
        trace[smt.reconstruct.sort] "{s} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct sort {s} with kind {s.getKind}"

@[export smt_reconstruct_term]
def reconstructTermImpl : cvc5.Term → ReconstructM Expr := withTermCache fun t => do
  withTraceNode ((`smt.reconstruct.term).str t.getKind.toString) (traceReconstructTerm t) do
    let rs := termRcons
    go rs t
where
  withTermCache (r : cvc5.Term → ReconstructM Expr) (t : cvc5.Term) : ReconstructM Expr := do
    match (← get).termCache[t]? with
    -- TODO: cvc5's global bound variables mess up the cache. Find a better fix.
    | some e => return e
    | none   => reconstruct r t
  reconstruct r t := do
    let e ← r t
    modify fun state => { state with termCache := state.termCache.insert t e }
    return e
  go (rs : List (TermReconstructor × Name)) (t : cvc5.Term) : ReconstructM Expr := do
    for (r, n) in rs do
      if let some e ← r t then
        trace[smt.reconstruct.term] "{t} =({n})=> {e}"
        return e
    throwError "Failed to reconstruct term {t} with kind {t.getKind}"

open Qq in
@[export smt_reconstruct_terms]
def reconstructTermsImpl (u) (α : Q(Type $u)) (ts : Array cvc5.Term) : ReconstructM Q(List $α) :=
  let f := fun t ys => do
    let a : Q($α) ← reconstructTerm t
    return q($a :: $ys)
  ts.foldrM f q([])

@[export smt_reconstruct_proof]
partial def reconstructProofImpl : cvc5.Proof → ReconstructM Expr := withProofCache fun pf => do
  let rs := proofRcons
  go rs pf
where
  go (rs : List (ProofReconstructor × Name)) (pf : cvc5.Proof) : ReconstructM Expr :=
  withTraceNode ((`smt.reconstruct.proof).str pf.getRule.toString) traceReconstructStep do
    for (r, _) in rs do
      if let some e ← r pf then
        return e
    _ ← pf.getChildren.mapM reconstructProof
    let type ← reconstructTerm pf.getResult
    addTrust type pf

end Reconstruct

def traceReconstructProof (r : Except Exception (List Expr × List Expr × Expr × Expr × List MVarId)) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Qq in
partial def reconstructProof (pf : cvc5.Proof) (ctx : Reconstruct.Context) :
  MetaM (List Expr × List Expr × Expr × Expr × List MVarId) :=
  withTraceNode `smt.reconstruct.proof traceReconstructProof do
  let (dfns, state) ← (pf.getArguments.toList.mapM Reconstruct.reconstructTerm).run ctx {}
  let (ps, state) ← (pf.getChildren[0]!.getArguments.toList.mapM Reconstruct.reconstructTerm).run ctx state
  let ((p : Q(Prop)), state) ← (Reconstruct.reconstructTerm (pf.getResult)).run ctx state
  let (h, ⟨_, _, _, _, mvs⟩) ← (Reconstruct.reconstructProof pf).run ctx state
  if dfns.isEmpty then
    let h : Q(True → $p) ← pure h
    return (dfns, ps, p, q($h trivial), mvs.toList)
  else
    return (dfns, ps, p, h, mvs.toList)

open cvc5 in
def traceSolve (r : Except Exception (Except SolverError Proof)) : MetaM MessageData :=
  return match r with
  | .ok (.ok _) => m!"{checkEmoji}"
  | _           => m!"{bombEmoji}"

open cvc5 in
def solve (query : String) (timeout : Option Nat) : MetaM (Except Error cvc5.Proof) :=
  profileitM Exception "simp" {} do
  withTraceNode `smt.solve traceSolve do Solver.run (← TermManager.new) do
    if let .some timeout := timeout then
      Solver.setOption "tlimit" (toString (1000*timeout))
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "simplification" "none"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "cegqi-midpoint" "true"
    Solver.setOption "produce-models" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parseCommands query
    let r ← Solver.checkSat
    trace[smt.solve] m!"result: {r}"
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        trace[smt.solve] "proof:\n{← Solver.proofToString ps[0]}"
        return ps[0]
    throw (self := instMonadExceptOfMonadExceptOf _ _) (Error.error s!"Expected unsat, got {r}")

syntax (name := reconstruct) "reconstruct" str : tactic

open Lean.Elab Tactic in
@[tactic reconstruct] def evalReconstruct : Tactic := fun stx =>
  withMainContext do
    let some query := stx[1].isStrLit? | throwError "expected string"
    let r ← solve query none
    match r with
      | .error e => logInfo (repr e)
      | .ok pf =>
        let (_, _, p, hp, mvs) ← reconstructProof pf ⟨(← getUserNames), false⟩
        let mv ← Tactic.getMainGoal
        let mv ← mv.assert (Name.num `s 0) p hp
        let (_, mv) ← mv.intro1
        replaceMainGoal (mv :: mvs)
where
  getUserNames : MetaM (Std.HashMap String FVarId) := do
    let lCtx ← getLCtx
    return lCtx.getFVarIds.foldl (init := {}) fun m fvarId =>
      m.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString fvarId

end Smt
