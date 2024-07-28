import Smt.Reconstruction.Certifying.Arith.TransFns.ArithTransApproxAboveBelow
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


theorem arithTransExpApproxBelow₁ (d n : ℕ) (h : d = 2*n + 1) (hx : 0 < x) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    sorry

theorem arithTransExpApproxBelow₂ (d n : ℕ) (h : d = 2*n + 1) (hx : x < 0) :
    Real.exp x ≥ taylorWithinEval Real.exp d Set.univ 0 x := by
    sorry
