import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Schoenfeld's explicit Chebyshev bound: statements

`Chebyshev.psi` and `RiemannHypothesis` are Mathlib's.
-/

namespace SchoenfeldRH

/-- Schoenfeld's bound, non-strict form: `|ψ(x) - x| ≤ √x (log x)² / (8π)` for all real `x ≥ 73.2`. -/
def SchoenfeldBound : Prop :=
  ∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

/-- Schoenfeld's bound, strict form (as in Schoenfeld 1976, Theorem 10). -/
def SchoenfeldBoundStrict : Prop :=
  ∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

theorem SchoenfeldBoundStrict.schoenfeldBound (h : SchoenfeldBoundStrict) : SchoenfeldBound :=
  fun x hx => (h x hx).le

end SchoenfeldRH
