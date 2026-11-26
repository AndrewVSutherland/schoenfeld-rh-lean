import SchoenfeldRH.Lemmas.p4.DigammaAux
import SchoenfeldRH.ZeroSum.Basic

/-!
# The partial-fraction expansion of `-ζ'/ζ`

`trivZero k = -2 (k + 1)` are the trivial zeros of `ζ`.
-/

open Complex

namespace SchoenfeldRH.Explicit

noncomputable def trivZero (k : ℕ) : ℂ := -(2 * ((k : ℂ) + 1))

lemma trivZero_re (k : ℕ) : (trivZero k).re = -(2 * ((k : ℝ) + 1)) := by
  simp [trivZero]

lemma trivZero_ne_zero (k : ℕ) : trivZero k ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [trivZero_re] at this
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma norm_trivZero (k : ℕ) : ‖trivZero k‖ = 2 * ((k : ℝ) + 1) := by
  have : trivZero k = ((-(2 * ((k : ℝ) + 1)) : ℝ) : ℂ) := by simp [trivZero]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]

theorem hasSum_trivZero {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / (s - trivZero k) + 1 / trivZero k)
      (-(1 / 2 * digamma (s / 2) + Real.eulerMascheroniConstant / 2 + 1 / s)) := by
  have hw : 1 / 2 < (s / 2 + 1).re := by
    simp
    linarith
  have h := (P4.hasSum_digamma hw).mul_left (-(1 / 2))
  have hs2 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [digamma_apply_add_one _ hs2, digamma_one] at h
  convert h using 1
  · funext k
    have hk : (k : ℂ) + 1 ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk2 : (k : ℂ) + (s / 2 + 1) ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk3 : s - trivZero k ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp [trivZero] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk4 := trivZero_ne_zero k
    have e1 : s - trivZero k = 2 * ((k : ℂ) + (s / 2 + 1)) := by simp [trivZero]; ring
    have e2 : trivZero k = -(2 * ((k : ℂ) + 1)) := rfl
    rw [e1, e2]
    field_simp
    ring
  · field_simp
    ring

theorem neg_logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s)
      = (1 / (s - 1) + 1) - (Real.log (2 * Real.pi) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
            (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
        - ∑' k : ℕ, (1 / (s - trivZero k) + 1 / trivZero k) := by
  have hxi : riemannXi s ≠ 0 := by
    intro h
    have := (riemannXi_zero_re_mem h).2
    linarith
  rw [(hasSum_hadamard_riemannXi hxi).tsum_eq, (hasSum_trivZero (by linarith)).tsum_eq,
    logDeriv_riemannZeta_eq hs]
  have hlog4 : ((Real.log (4 * Real.pi) : ℝ) : ℂ) = 2 * (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 : ((Real.log (2 * Real.pi) : ℝ) : ℂ) = (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']; push_cast; ring
  have hc : (xiConst : ℂ) = 1 + (Real.eulerMascheroniConstant : ℂ) / 2
      - ((Real.log (4 * Real.pi) : ℝ) : ℂ) / 2 := by
    unfold xiConst; push_cast; ring
  rw [hc, hlog4, hlog2]
  ring

end SchoenfeldRH.Explicit
-- stamp: 1
