import SchoenfeldRH.ZeroSum.Basic
import SchoenfeldRH.ZeroSum.RealAxis

/-!
# The bound `B · W(B) ≤ log²(B/π)/(2π) + 1/2` for `B ≥ 50` under RH (Contract Z)

Notation: zeros `ρ = 1/2 + iγ` of `ξ = riemannXi` with multiplicity `m`, `P = ‖ρ‖ = √(1/4 + γ²)`,
`Q = ‖B + 1/2 - ρ‖ = √(B² + γ²)`, so that `W(B) = Σ m/(P Q)`.

The proof follows sections 1 and 2 of the blueprint, in the variable `t = tan(θ/2) ∈ [3/B, 1]`, and with
finite partial sums and a monotonicity argument in place of the interchange of `Σ_ρ` and `∫`:

* `g(t) = -arctan(P (1 - t²)/(2 Q t))/(P Q)` has `g(1) = 0`, `g'(t) = 2(1 + t²)/(P²(1 - t²)² + 4Q²t²)`, and
  `π/(2PQ) = arctan(2 Q t₁/(P (1 - t₁²)))/(P Q) - g(t₁) ≤ (2t₁/(1 - t₁²))/P² + (g(1) - g(t₁))`;
* `P²(1 - t²)² + 4Q²t² ≥ (1 + t²)²(γ² + u²)` with `u = 2Bt/(1 + t²)`, hence for a finite set `S` of zeros
  `Σ_S m g'(t) ≤ (1/(Bt)) Σ_S m u/(u² + γ²) ≤ (1/(Bt)) ξ'/ξ(u + 1/2)` (the Poisson-kernel sum);
* `ξ'/ξ(u + 1/2) ≤ ½ log(u/2π) + (7/3)/u` for `u ≥ 5/2` (`re_logDeriv_riemannXi_le`, in `ZeroSum/RealAxis.lean`), and
  `u ≤ 2Bt`, so `Σ_S m g'(t) ≤ Ψ'(t)`, `Ψ(t) = log²(Bt/π)/(4B) + (7/6)(t - 1/t)/B²`;
* therefore `Ψ - Σ_S m g` is monotone on `[3/B, 1]`, and
  `(π/2) Σ_S m/(PQ) ≤ (2t₁/(1 - t₁²))/20 + Ψ(1) - Ψ(t₁)` with `t₁ = 3/B`.

The constant obtained is `(2/π)(3/(10 (1 - 9/B²)) + 7/18) < 0.44`; `zeroSumW_le_of_RH'` states it as `9/20`.
-/

namespace SchoenfeldRH

open Complex

/-! ### Partial sums of the Poisson-kernel sum -/

/-- Partial sums of the Poisson-kernel sum: `Σ_{ρ ∈ S} m u/(u² + γ²) ≤ ½ log(u/2π) + (7/3)/u`, `u ≥ 5/2`. -/
theorem sum_poisson_le (hRH : RiemannHypothesis) {u : ℝ} (hu : 5 / 2 ≤ u)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + (ρ : ℂ).im ^ 2))
      ≤ Real.log (u / (2 * Real.pi)) / 2 + 7 / 3 / u := by
  have hu0 : 0 < u := by linarith
  refine (sum_le_hasSum S (fun ρ _ => ?_) (hasSum_poisson hRH hu0)).trans (re_logDeriv_riemannXi_le hu)
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hu0.le (by positivity))

/-! ### Calculus -/

/-- `g(t) = -arctan(P (1 - t²)/(2 Q t))/(P Q)`: an antiderivative of
`2(1 + t²)/(P²(1 - t²)² + 4Q²t²)` on `t > 0`. -/
noncomputable def gAux (P Q t : ℝ) : ℝ := -Real.arctan (P * (1 - t ^ 2) / (2 * Q * t)) / (P * Q)

theorem gAux_one (P Q : ℝ) : gAux P Q 1 = 0 := by simp [gAux]

theorem hasDerivAt_gAux {P Q t : ℝ} (hP : 0 < P) (hQ : 0 < Q) (ht : 0 < t) :
    HasDerivAt (gAux P Q) (2 * (1 + t ^ 2) / (P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2)) t := by
  have hn : HasDerivAt (fun t : ℝ => P * (1 - t ^ 2)) (P * (-(2 * t))) t := by
    have := ((hasDerivAt_pow 2 t).const_sub 1).const_mul P
    simpa using this
  have hd : HasDerivAt (fun t : ℝ => 2 * Q * t) (2 * Q) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Q)
  have h1 : HasDerivAt (fun t : ℝ => P * (1 - t ^ 2) / (2 * Q * t))
      ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2) t :=
    hn.fun_div hd (by positivity)
  have h2 : HasDerivAt (fun t : ℝ => -Real.arctan (P * (1 - t ^ 2) / (2 * Q * t)) / (P * Q))
      (-(1 / (1 + (P * (1 - t ^ 2) / (2 * Q * t)) ^ 2) *
        ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2)) / (P * Q)) t :=
    (h1.arctan.neg).div_const (P * Q)
  have hden : 0 < P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2 := by positivity
  have hden' : 0 < (2 * Q * t) ^ 2 + (P * (1 - t ^ 2)) ^ 2 := by positivity
  have e : 2 * (1 + t ^ 2) / (P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2)
      = -(1 / (1 + (P * (1 - t ^ 2) / (2 * Q * t)) ^ 2) *
        ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2)) / (P * Q) := by
    field_simp
    ring
  rw [e]
  exact h2

/-- `Ψ(t) = log²(Bt/π)/(4B) + C (t - 1/t)/(2B²)`. -/
noncomputable def psiAux (B C t : ℝ) : ℝ :=
  Real.log (B * t / Real.pi) ^ 2 / (4 * B) + C / (2 * B ^ 2) * (t - t⁻¹)

theorem hasDerivAt_psiAux {B C t : ℝ} (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (psiAux B C)
      (Real.log (B * t / Real.pi) / (2 * B * t) + C / (2 * B ^ 2) * (1 + 1 / t ^ 2)) t := by
  have hpi := Real.pi_pos
  have h0 : HasDerivAt (fun t : ℝ => B * t / Real.pi) (B / Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul B).div_const Real.pi
  have h1 : HasDerivAt (fun t : ℝ => Real.log (B * t / Real.pi) ^ 2)
      (((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi))) t :=
    (h0.log (by positivity)).fun_pow 2
  have h3 : HasDerivAt (fun t : ℝ => t - t⁻¹) (1 - -(t ^ 2)⁻¹) t :=
    (hasDerivAt_id t).fun_sub (hasDerivAt_inv ht.ne')
  have h4 : HasDerivAt (fun t : ℝ => Real.log (B * t / Real.pi) ^ 2 / (4 * B)
        + C / (2 * B ^ 2) * (t - t⁻¹))
      (((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi)) / (4 * B)
        + C / (2 * B ^ 2) * (1 - -(t ^ 2)⁻¹)) t :=
    (h1.div_const (4 * B)).fun_add (h3.const_mul (C / (2 * B ^ 2)))
  have e : Real.log (B * t / Real.pi) / (2 * B * t) + C / (2 * B ^ 2) * (1 + 1 / t ^ 2)
      = ((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi)) / (4 * B)
        + C / (2 * B ^ 2) * (1 - -(t ^ 2)⁻¹) := by
    norm_num
    field_simp
    ring
  rw [e]
  exact h4

/-! ### The comparison of derivatives -/

/-- For `B ≥ 50` and `3/B ≤ t ≤ 1`: `Σ_{ρ ∈ S} m g_ρ'(t) ≤ Ψ'(t)` (with `C = 7/3`). -/
theorem sum_deriv_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 50 ≤ B)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) {t : ℝ} (ht1 : 3 / B ≤ t) (ht2 : t ≤ 1) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))
      ≤ Real.log (B * t / Real.pi) / (2 * B * t) + 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2) := by
  have hB0 : 0 < B := by linarith
  have hpi := Real.pi_pos
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hBt : 3 ≤ B * t := by
    have := mul_le_mul_of_nonneg_left ht1 hB0.le
    rwa [mul_div_cancel₀ _ hB0.ne'] at this
  set u : ℝ := 2 * B * t / (1 + t ^ 2) with hu
  have hu3 : 5 / 2 ≤ u := by
    rw [hu, le_div_iff₀ (by positivity)]
    nlinarith
  have hu0 : 0 < u := by linarith
  have hS := sum_poisson_le hRH hu3 S
  -- termwise comparison
  have hterm : ∀ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))
      ≤ 1 / (B * t) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + (ρ : ℂ).im ^ 2))) := by
    intro ρ _
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    rw [norm_sq_of_re_eq_half hρ, norm_sq_shift_sub hρ B]
    set γ := (ρ : ℂ).im
    have e : 1 / (B * t) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + γ ^ 2)))
        = (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
          (2 * (1 + t ^ 2) / (γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2)) := by
      have h1 : 0 < u ^ 2 + γ ^ 2 := by positivity
      have h2 : 0 < γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2 := by positivity
      have h3 : u ^ 2 + γ ^ 2 = (γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2) / (1 + t ^ 2) ^ 2 := by
        rw [hu]; field_simp; ring
      rw [h3, hu]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg (1 - t ^ 2)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hBt0 : 0 < B * t := by positivity
  have h1 : 1 / (B * t) * ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
      (u / (u ^ 2 + (ρ : ℂ).im ^ 2)) ≤ 1 / (B * t) * (Real.log (u / (2 * Real.pi)) / 2 + 7 / 3 / u) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  refine h1.trans ?_
  have hlog : Real.log (u / (2 * Real.pi)) ≤ Real.log (B * t / Real.pi) := by
    refine Real.log_le_log (by positivity) ?_
    rw [hu, div_div, div_le_div_iff₀ (by positivity) hpi]
    nlinarith [mul_pos hBt0 hpi, sq_nonneg t]
  have e2 : 1 / (B * t) * (7 / 3 / u) = 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2) := by
    rw [hu]; field_simp; ring
  have e3 : 1 / (B * t) * (Real.log (u / (2 * Real.pi)) / 2)
      ≤ Real.log (B * t / Real.pi) / (2 * B * t) := by
    rw [show Real.log (B * t / Real.pi) / (2 * B * t)
        = 1 / (B * t) * (Real.log (B * t / Real.pi) / 2) by field_simp]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [mul_add, e2]
  linarith

/-! ### Partial sums of `W(B)` -/

/-- The partial sums of `(π/2) W(B)`. -/
theorem sum_zeroSumW_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 50 ≤ B)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) :
    Real.pi / 2 * ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)
      ≤ 2 * (3 / B) / (1 - (3 / B) ^ 2) * (1 / 20) + (psiAux B (7 / 3) 1 - psiAux B (7 / 3) (3 / B)) := by
  have hB0 : 0 < B := by linarith
  set t₁ : ℝ := 3 / B with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁1 : t₁ < 1 := by rw [ht₁, div_lt_one hB0]; linarith
  have ht₁sq : 0 < 1 - t₁ ^ 2 := by nlinarith
  have hPpos : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, 0 < ‖(ρ : ℂ)‖ := fun ρ =>
    norm_pos_iff.2 (riemannXi_zero_ne_zero ρ.2)
  have hQpos : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, 0 < ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ := fun ρ => by
    have h := norm_sq_shift_sub (riemannXi_zero_re_of_RH hRH ρ.2) B
    have : 0 < ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 := by rw [h]; positivity
    have hne : ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ≠ 0 := fun h0 => by rw [h0] at this; norm_num at this
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  -- the monotone function
  set F : ℝ → ℝ := fun t => psiAux B (7 / 3) t - ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
    gAux ‖(ρ : ℂ)‖ ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ t with hF
  have hFd : ∀ t : ℝ, 0 < t → HasDerivAt F
      ((Real.log (B * t / Real.pi) / (2 * B * t) + 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2))
        - ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))) t := by
    intro t ht
    exact (hasDerivAt_psiAux hB0 ht).sub
      (HasDerivAt.fun_sum fun ρ _ => (hasDerivAt_gAux (hPpos ρ) (hQpos ρ) ht).const_mul _)
  have hmono : MonotoneOn F (Set.Icc t₁ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)
    · exact (hFd t (lt_of_lt_of_le ht₁0 ht.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at ht
      exact (hFd t (lt_trans ht₁0 ht.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hFd t (lt_trans ht₁0 ht.1)).deriv, sub_nonneg]
      exact sum_deriv_le hRH hB S ht.1.le ht.2.le
  have hF1 := hmono (Set.left_mem_Icc.mpr ht₁1.le) (Set.right_mem_Icc.mpr ht₁1.le) ht₁1.le
  simp only [hF, gAux_one, mul_zero, Finset.sum_const_zero, sub_zero] at hF1
  -- termwise: `π/(2PQ) ≤ (2t₁/(1-t₁²)) /P² - g(t₁)`
  have hterm : ∀ ρ ∈ S, Real.pi / 2 * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖))
      ≤ 2 * t₁ / (1 - t₁ ^ 2) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2)
        - (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
          gAux ‖(ρ : ℂ)‖ ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ t₁ := by
    intro ρ _
    have hP := hPpos ρ
    have hQ := hQpos ρ
    set P := ‖(ρ : ℂ)‖
    set Q := ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖
    set m : ℝ := (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ)
    have hm : 0 ≤ m := Nat.cast_nonneg _
    set x : ℝ := P * (1 - t₁ ^ 2) / (2 * Q * t₁) with hx
    have hx0 : 0 < x := by positivity
    have h1 : Real.pi / 2 - Real.arctan x ≤ x⁻¹ := by
      rw [← Real.arctan_inv_of_pos hx0]
      exact Real.arctan_le_self (by positivity)
    have h2 : Real.pi / 2 * (m / (P * Q)) = m / (P * Q) * (Real.pi / 2 - Real.arctan x)
        - m * gAux P Q t₁ := by
      rw [gAux, ← hx]; ring
    have h3 : m / (P * Q) * x⁻¹ = 2 * t₁ / (1 - t₁ ^ 2) * (m / P ^ 2) := by
      rw [hx]; field_simp
    rw [h2, ← h3]
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ m / (P * Q) by positivity)
    linarith
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    ((summable_zero_inv_norm_sq hRH).sum_le_tsum S (fun ρ _ => by positivity)).trans
      (tsum_zero_inv_norm_sq_le hRH)
  have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * t₁ / (1 - t₁ ^ 2) by positivity)
  linarith

/-- Under the Riemann hypothesis, `B · W(B) ≤ log²(B/π)/(2π) + 9/20` for `B ≥ 50`
(what the argument gives, rounded up; the true constant is about `0.23`). -/
theorem zeroSumW_le_of_RH' (hRH : RiemannHypothesis) (B : ℝ) (hB : 50 ≤ B) :
    B * zeroSumW B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20 := by
  have hB0 : 0 < B := by linarith
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_d2
  have key : zeroSumW B ≤ (Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20) / B := by
    refine Real.tsum_le_of_sum_le (fun ρ => zeroSumW_term_nonneg B ρ) fun S => ?_
    have h := sum_zeroSumW_le hRH hB S
    set T := ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)
    set L := Real.log (B / Real.pi)
    -- the first term
    have h1 : 2 * (3 / B) / (1 - (3 / B) ^ 2) * (1 / 20) ≤ 31 / 100 / B := by
      have hx0 : 0 < 3 / B := by positivity
      have hx1 : 3 / B ≤ 3 / 50 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hB
      have hxB : 3 / B * B = 3 := div_mul_cancel₀ _ hB0.ne'
      have hx2 : (3 / B) ^ 2 ≤ 9 / 2500 := by nlinarith
      have hd : 0 < 1 - (3 / B) ^ 2 := by linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hd hB0,
        show 2 * (3 / B) * (1 / 20) * B = 3 / B * B / 10 by ring, hxB]
      linarith
    -- the second term
    have h2 : psiAux B (7 / 3) 1 - psiAux B (7 / 3) (3 / B) ≤ L ^ 2 / (4 * B) + 7 / 18 / B := by
      unfold psiAux
      rw [mul_one, mul_div_cancel₀ _ hB0.ne']
      have hsq : 0 ≤ Real.log (3 / Real.pi) ^ 2 / (4 * B) := by positivity
      have e : 7 / 3 / (2 * B ^ 2) * (1 - 1⁻¹) - 7 / 3 / (2 * B ^ 2) * (3 / B - (3 / B)⁻¹)
          = 7 / 18 / B - 7 / (2 * B ^ 3) := by
        field_simp; ring
      have hpos : 0 ≤ 7 / (2 * B ^ 3) := by positivity
      linarith
    rw [le_div_iff₀ hB0]
    have h3 : Real.pi / 2 * T ≤ (L ^ 2 / 4 + 7 / 10) / B := by
      have : 31 / 100 / B + (L ^ 2 / (4 * B) + 7 / 18 / B) ≤ (L ^ 2 / 4 + 7 / 10) / B := by
        rw [show 31 / 100 / B + (L ^ 2 / (4 * B) + 7 / 18 / B) = (L ^ 2 / 4 + 31 / 100 + 7 / 18) / B by
          field_simp; ring]
        exact div_le_div_of_nonneg_right (by linarith) hB0.le
      linarith
    rw [le_div_iff₀ hB0] at h3
    -- `T B ≤ (2/π)(L²/4 + 7/10) ≤ L²/(2π) + 9/20`
    have h4 : T * B ≤ 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) := by
      rw [show T * B = 2 / Real.pi * (Real.pi / 2 * T * B) by field_simp]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) ≤ L ^ 2 / (2 * Real.pi) + 9 / 20 := by
      rw [show 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) = L ^ 2 / (2 * Real.pi) + 7 / 5 / Real.pi by
        field_simp; ring]
      have : 7 / 5 / Real.pi ≤ 9 / 20 := by
        rw [div_le_div_iff₀ hpi (by norm_num)]; linarith
      linarith
    linarith
  calc B * zeroSumW B
      ≤ B * ((Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20) / B) :=
        mul_le_mul_of_nonneg_left key hB0.le
    _ = Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20 := by field_simp

/-- **Contract Z.** Under the Riemann hypothesis, `B · W(B) ≤ log²(B/π)/(2π) + 1/2` for `B ≥ 50`. -/
theorem zeroSumW_le_of_RH (hRH : RiemannHypothesis) (B : ℝ) (hB : 50 ≤ B) :
    B * zeroSumW B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2 := by
  have := zeroSumW_le_of_RH' hRH B hB
  linarith

end SchoenfeldRH
