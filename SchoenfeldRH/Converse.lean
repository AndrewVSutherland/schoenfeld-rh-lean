import SchoenfeldRH.Defs
import SchoenfeldRH.Converse.PsiBigO
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Schoenfeld's bound implies the Riemann Hypothesis

Schoenfeld's bound `|ψ(x) - x| ≤ √x (log x)² / (8π)` (for `x ≥ 73.2`) gives
`ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`, because `(log x)² = o(x ^ ε)`. The converse
theorem `riemannHypothesis_of_chebyshev_psi_sub_isBigO` (ported in
`SchoenfeldRH.Converse.PsiBigO`) then yields Mathlib's `RiemannHypothesis`.

## Main results

* `SchoenfeldRH.psi_sub_isBigO_rpow_of_schoenfeldBound`: the `O(x ^ (1 / 2 + ε))` consequence.
* `SchoenfeldRH.riemannHypothesis_of_schoenfeldBound`: `SchoenfeldBound → RiemannHypothesis`.
* `SchoenfeldRH.riemannHypothesis_of_schoenfeldBoundStrict`: the same for the strict bound.
-/

open Filter Asymptotics

namespace SchoenfeldRH

/-- Schoenfeld's bound implies `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`. -/
theorem psi_sub_isBigO_rpow_of_schoenfeldBound (h : SchoenfeldBound) (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  have hlog : (fun x : ℝ => Real.log x ^ 2) =O[atTop] fun x : ℝ => x ^ ε := by
    have h0 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε).isBigO
    simpa only [Real.rpow_two] using h0
  have hmul : (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) =O[atTop]
      fun x : ℝ => Real.sqrt x * x ^ ε :=
    (isBigO_refl (fun x : ℝ => Real.sqrt x) atTop).mul hlog
  have hdiv : (fun x : ℝ => Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) =O[atTop]
      fun x : ℝ => Real.sqrt x * x ^ ε :=
    (hmul.const_mul_left (8 * Real.pi)⁻¹).congr_left fun x => (div_eq_inv_mul _ _).symm
  have hrpow : (fun x : ℝ => Real.sqrt x * x ^ ε) =ᶠ[atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_add hx, Real.sqrt_eq_rpow]
  have hψ : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (73.2 : ℝ)] with x hx
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (h x hx).trans (le_abs_self _)
  exact (hψ.trans hdiv).congr' EventuallyEq.rfl hrpow

/-- **Schoenfeld's bound implies the Riemann Hypothesis.** -/
theorem riemannHypothesis_of_schoenfeldBound (h : SchoenfeldBound) : RiemannHypothesis :=
  riemannHypothesis_of_chebyshev_psi_sub_isBigO (psi_sub_isBigO_rpow_of_schoenfeldBound h)

/-- The strict form of Schoenfeld's bound implies the Riemann Hypothesis. -/
theorem riemannHypothesis_of_schoenfeldBoundStrict (h : SchoenfeldBoundStrict) :
    RiemannHypothesis :=
  riemannHypothesis_of_schoenfeldBound h.schoenfeldBound

end SchoenfeldRH
