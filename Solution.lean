import SchoenfeldRH.Main

/-!
# Solution: Schoenfeld's bound is equivalent to the Riemann hypothesis

The theorem name and statement are identical to `Challenge.lean`; judged by `lake comparator` with
`comparator.json`. `SchoenfeldBoundStrict` unfolds to the challenge's left-hand side.
-/

theorem schoenfeld_strict_bound_iff_riemannHypothesis :
    (∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ↔
      RiemannHypothesis :=
  SchoenfeldRH.schoenfeldBoundStrict_iff_riemannHypothesis
