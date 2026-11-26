import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Riemann's entire function `ξ`: zeros and special values

`Complex.riemannXi s = (s (s - 1) Λ₀(s) + 1) / 2` is defined in the vendored PrimeNumberTheoremAnd module
`Mathlib/Analysis/SpecialFunctions/CompletedXi.lean`, where it is shown to be entire and to satisfy
`ξ(1 - s) = ξ(s)`. This file adds: its zeros lie in the open critical strip, and the values of `ξ'/ξ` at 0 and 1.
-/

open Complex

namespace SchoenfeldRH

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

private lemma riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [riemannXi_one]; norm_num
  have h0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero h0] at hζ
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    exact hζ (by rw [h, zero_div])
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hΛ) two_ne_zero

/-- Every zero of `ξ` lies in the open critical strip. -/
theorem riemannXi_eq_zero_re {ρ : ℂ} (h : riemannXi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hc
    have h1 : 1 ≤ (1 - ρ).re := by
      simp only [sub_re, one_re]
      linarith [not_lt.mp hc]
    exact riemannXi_ne_zero_of_one_le_re h1 (by rw [riemannXi_one_sub, h])
  · by_contra hc
    exact riemannXi_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- The zero set of `ξ` is countable. -/
theorem countable_riemannXi_zeros : Countable {ρ : ℂ // riemannXi ρ = 0} := by
  have hana : AnalyticOnNhd ℂ riemannXi Set.univ :=
    (analyticOnNhd_univ_iff_differentiable).mpr differentiable_riemannXi
  have h0 : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have hcod : (riemannXi ⁻¹' {0})ᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) :=
    hana.preimage_zero_mem_codiscrete h0
  have hdisc := isDiscrete_of_codiscreteWithin hcod
  have hc : (riemannXi ⁻¹' {0} ∩ Set.univ).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  rw [Set.inter_univ] at hc
  exact hc.to_subtype

private lemma hasDerivAt_riemannXi (s : ℂ) :
    HasDerivAt riemannXi
      (((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s +
        s * (s - 1) * deriv completedRiemannZeta₀ s) / 2) s := by
  have hΛ : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ s) s :=
    (differentiable_completedZeta₀ s).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have h2 := ((h1.mul hΛ).add_const 1).div_const 2
  exact h2

/-- `ξ'/ξ(1) = 1 + γ/2 - log(4π)/2`. -/
theorem logDeriv_riemannXi_one :
    logDeriv riemannXi 1 =
      ((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  rw [logDeriv_apply, (hasDerivAt_riemannXi 1).deriv, riemannXi_one, completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hlog]
  push_cast
  ring

/-- `ξ'/ξ(0) = -ξ'/ξ(1)`. -/
theorem logDeriv_riemannXi_zero :
    logDeriv riemannXi 0 =
      -((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
    have := completedRiemannZeta₀_one_sub 1
    simpa using this
  rw [logDeriv_apply, (hasDerivAt_riemannXi 0).deriv, riemannXi_zero, h01,
    completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hlog]
  push_cast
  ring

end SchoenfeldRH
