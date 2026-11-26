import SchoenfeldRH.Xi.Compat
import SchoenfeldRH.ZeroSum.Defs

/-!
# Zeros of `ξ` under the Riemann hypothesis, and the Hadamard sum for `ξ'/ξ`

`zeroSumW` is defined in `SchoenfeldRH/ZeroSum/Defs.lean`.
-/

namespace SchoenfeldRH

open Complex

theorem riemannXi_zero_re_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (h : riemannXi ρ = 0) : ρ.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_re_mem h
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [riemannXi_eq_mul_completedRiemannZeta hρ0 hρ1] at h
  have hΛ : completedRiemannZeta ρ = 0 := by
    have h' : ρ * (ρ - 1) * completedRiemannZeta ρ = 0 := by
      rcases div_eq_zero_iff.1 h with h | h
      · exact h
      · exact absurd h two_ne_zero
    rcases mul_eq_zero.1 h' with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.1 h) hρ1
    · exact h
  apply hRH ρ
  · rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hρ1

theorem riemannXi_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : s.re ≠ 1 / 2) : riemannXi s ≠ 0 :=
  fun h => hs (riemannXi_zero_re_of_RH hRH h)

theorem riemannXi_zero_ne_zero {ρ : ℂ} (h : riemannXi ρ = 0) : ρ ≠ 0 := by
  rintro rfl
  rw [riemannXi_zero] at h
  norm_num at h

theorem norm_sq_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, hρ]
  ring

theorem norm_sq_shift_sub {ρ : ℂ} (hρ : ρ.re = 1 / 2) (B : ℝ) :
    ‖((B : ℂ) + 1 / 2) - ρ‖ ^ 2 = B ^ 2 + ρ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [hρ]
  ring

/-- For `ρ = 1/2 + iy`: `1/(1 - ρ) + 1/ρ = 1/(1/4 + y²)`. -/
theorem one_sub_inv_add_inv_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / (1 - ρ) + 1 / ρ = ((1 / (1 / 4 + ρ.im ^ 2) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < 1 / 4 + ρ.im ^ 2 := by positivity
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hρ; norm_num at hρ
  have hρ1 : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hρ] at this
    norm_num at this
  have key : ρ * (1 - ρ) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hρ, pow_two] <;> ring
  have hne : ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.ofReal_div, Complex.ofReal_one, ← key]
  field_simp
  ring

theorem hasSum_zero_inv_norm_sq (hRH : RiemannHypothesis) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2)
      (2 * xiConst) := by
  have h1 := hasSum_hadamard_riemannXi (s := 1) (by rw [riemannXi_one]; norm_num)
  rw [deriv_div_riemannXi_one] at h1
  have h2 := Complex.hasSum_re h1
  have e : ((xiConst : ℂ) + (xiConst : ℂ)).re = 2 * xiConst := by simp; ring
  rw [e] at h2
  convert h2 using 1
  funext ρ
  have hre := riemannXi_zero_re_of_RH hRH ρ.2
  rw [norm_sq_of_re_eq_half hre, one_sub_inv_add_inv_of_re_eq_half hre, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem summable_zero_inv_norm_sq (hRH : RiemannHypothesis) :
    Summable (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
  (hasSum_zero_inv_norm_sq hRH).summable

theorem tsum_zero_inv_norm_sq_le (hRH : RiemannHypothesis) :
    ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 := by
  rw [(hasSum_zero_inv_norm_sq hRH).tsum_eq]
  exact two_mul_xiConst_lt.le

/-- For `ρ = 1/2 + iy` and real `β > 0`: `Re (1/(β + 1/2 - ρ) + 1/ρ) = β/(β² + y²) + (1/2)/(1/4 + y²)`. -/
theorem re_inv_shift_sub_add_inv {ρ : ℂ} (hρ : ρ.re = 1 / 2) {β : ℝ} (hβ : 0 < β) :
    (1 / (((β + 1 / 2 : ℝ) : ℂ) - ρ) + 1 / ρ).re
      = β / (β ^ 2 + ρ.im ^ 2) + 1 / 2 * (1 / (1 / 4 + ρ.im ^ 2)) := by
  have hpos : (0 : ℝ) < 1 / 4 + ρ.im ^ 2 := by positivity
  have hpos2 : (0 : ℝ) < β ^ 2 + ρ.im ^ 2 := by positivity
  have n1 : Complex.normSq (((β + 1 / 2 : ℝ) : ℂ) - ρ) = β ^ 2 + ρ.im ^ 2 := by
    simp [Complex.normSq_apply, hρ]; ring
  have n2 : Complex.normSq ρ = 1 / 4 + ρ.im ^ 2 := by
    simp [Complex.normSq_apply, hρ]; ring
  have e1 : (1 / (((β + 1 / 2 : ℝ) : ℂ) - ρ)).re = β / (β ^ 2 + ρ.im ^ 2) := by
    rw [one_div, Complex.inv_re, n1, Complex.sub_re, Complex.ofReal_re, hρ]
    ring
  have e2 : (1 / ρ).re = 1 / 2 * (1 / (1 / 4 + ρ.im ^ 2)) := by
    rw [one_div, Complex.inv_re, n2, hρ]
    ring
  rw [Complex.add_re, e1, e2]

theorem hasSum_poisson (hRH : RiemannHypothesis) {β : ℝ} (hβ : 0 < β) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℝ) * (β / (β ^ 2 + (ρ : ℂ).im ^ 2)))
      (deriv riemannXi ((β + 1 / 2 : ℝ) : ℂ) / riemannXi ((β + 1 / 2 : ℝ) : ℂ)).re := by
  have hs : riemannXi ((β + 1 / 2 : ℝ) : ℂ) ≠ 0 := by
    apply riemannXi_ne_zero_of_RH hRH
    rw [Complex.ofReal_re]
    linarith
  have h1 := Complex.hasSum_re (hasSum_hadamard_riemannXi hs)
  have h2 := (hasSum_zero_inv_norm_sq hRH).mul_left (1 / 2)
  have h3 := h1.sub h2
  convert h3 using 1
  · funext ρ
    have hre := riemannXi_zero_re_of_RH hRH ρ.2
    rw [norm_sq_of_re_eq_half hre, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      re_inv_shift_sub_add_inv hre hβ]
    ring
  · simp

theorem zeroSumW_term_nonneg (B : ℝ) (ρ : {ρ : ℂ // riemannXi ρ = 0}) :
    0 ≤ (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖) := by
  positivity

theorem summable_zeroSumW (hRH : RiemannHypothesis) (B : ℝ) (hB : 0 < B) :
    Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖) := by
  set c : ℝ := min 1 (2 * B) with hc
  have hc0 : 0 < c := lt_min one_pos (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : c ≤ 2 * B := min_le_right _ _
  refine Summable.of_nonneg_of_le (fun ρ => zeroSumW_term_nonneg B ρ) (fun ρ => ?_)
    ((summable_zero_inv_norm_sq hRH).mul_left (1 / c))
  have hre := riemannXi_zero_re_of_RH hRH ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := riemannXi_zero_ne_zero ρ.2
  have hn : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  have e1 := norm_sq_of_re_eq_half hre
  have e2 := norm_sq_shift_sub hre B
  set a := ‖(ρ : ℂ)‖
  set d := ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖
  set y := (ρ : ℂ).im
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsq : (c * a) ^ 2 ≤ d ^ 2 := by
    rw [mul_pow, e1, e2]
    have : c ^ 2 ≤ 1 := by nlinarith
    have : c ^ 2 ≤ 4 * B ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  have hcd : c * a ≤ d := by nlinarith [mul_pos hc0 hn]
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannXi ρ : ℝ) := Nat.cast_nonneg _
  have hdpos : 0 < d := lt_of_lt_of_le (mul_pos hc0 hn) hcd
  rw [div_le_iff₀ (mul_pos hn hdpos), show 1 / c * ((analyticOrderNatAt riemannXi ρ : ℝ) / a ^ 2) * (a * d)
    = (analyticOrderNatAt riemannXi ρ : ℝ) * (d / (c * a)) by field_simp]
  have : 1 ≤ d / (c * a) := by rw [le_div_iff₀ (by positivity)]; linarith
  nlinarith

theorem zeroSumW_nonneg (B : ℝ) : 0 ≤ zeroSumW B :=
  tsum_nonneg (fun ρ => zeroSumW_term_nonneg B ρ)

end SchoenfeldRH
-- stamp: 2
