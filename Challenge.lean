import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Challenge: Schoenfeld's bound is equivalent to the Riemann hypothesis

Imports only Mathlib. `Chebyshev.psi` and `RiemannHypothesis` are Mathlib's.
Judged by `lake comparator` with `comparator.json`.
-/

theorem schoenfeld_strict_bound_iff_riemannHypothesis :
    (∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ↔
      RiemannHypothesis := by
  sorry
