import SchoenfeldRH.Defs
import SchoenfeldRH.Converse
import SchoenfeldRH.LargeRH
import SchoenfeldRH.Small

/-!
# Schoenfeld's bound `|ψ(x) - x| ≤ √x (log x)² / (8π)` for `x ≥ 73.2` is equivalent to the Riemann hypothesis

* `SchoenfeldRH.schoenfeldBound_iff_riemannHypothesis`: the non-strict bound (`SchoenfeldBound`) is equivalent to
  Mathlib's `RiemannHypothesis`.
* `SchoenfeldRH.schoenfeldBoundStrict_iff_riemannHypothesis`: so is the strict bound (Schoenfeld 1976, Theorem 10, (6.2)).

Forward direction: for `x ≥ 30000`, `schoenfeld_large_of_RH` (smoothed explicit formulas with the kernel
`μ x^s / (s (s + μ))`, the zero sum `zeroSumW` bounded through the Poisson-kernel identity for `ξ'/ξ`; no zero counting);
for `73.2 ≤ x ≤ 30000`, `schoenfeld_small` (one kernel-checked walk in exact natural-number arithmetic).
Converse: `riemannHypothesis_of_schoenfeldBound`.
The only Lake dependency is Mathlib; the vendored library `Vendor` (Hadamard factorization, Apache-2.0) lives in this
repository.
-/

namespace SchoenfeldRH

/-- RH implies Schoenfeld's strict bound for `ψ` (Schoenfeld 1976, Theorem 10, (6.2)). -/
theorem schoenfeldBoundStrict_of_riemannHypothesis (hRH : RiemannHypothesis) : SchoenfeldBoundStrict := by
  intro x hx
  rcases le_or_gt x 30000 with h | h
  · exact schoenfeld_small x hx h
  · exact schoenfeld_large_of_RH hRH x h.le

/-- RH implies Schoenfeld's bound for `ψ` in the non-strict form. -/
theorem schoenfeldBound_of_riemannHypothesis (hRH : RiemannHypothesis) : SchoenfeldBound :=
  (schoenfeldBoundStrict_of_riemannHypothesis hRH).schoenfeldBound

/-- **Schoenfeld's bound (non-strict) is equivalent to the Riemann hypothesis.** -/
theorem schoenfeldBound_iff_riemannHypothesis : SchoenfeldBound ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_schoenfeldBound, schoenfeldBound_of_riemannHypothesis⟩

/-- **Schoenfeld's bound (strict) is equivalent to the Riemann hypothesis.** -/
theorem schoenfeldBoundStrict_iff_riemannHypothesis : SchoenfeldBoundStrict ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_schoenfeldBoundStrict, schoenfeldBoundStrict_of_riemannHypothesis⟩

end SchoenfeldRH
