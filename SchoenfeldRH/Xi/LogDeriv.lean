import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# `ζ'/ζ` in terms of `ξ'/ξ`, and a numerical bound

For `Re s > 1`, `ξ(s) = s (s - 1) π^(-s/2) Γ(s/2) ζ(s) / 2`, hence
`ζ'/ζ(s) = ξ'/ξ(s) - 1/s - 1/(s - 1) + (log π)/2 - ψ(s/2)/2` with `ψ = Γ'/Γ` (`Complex.digamma`).
-/

open Complex

namespace SchoenfeldRH

private theorem harmonic_256_le : harmonic 256 ≤ 61244/10000 := by
  rw [harmonic]; decide +kernel

theorem logDeriv_riemannZeta_eq_logDeriv_riemannXi {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s =
      logDeriv riemannXi s - 1 / s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 - digamma (s / 2) / 2 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hG : Gamma (s / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simp; linarith
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp at h'
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hP : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    simp [hπ]
  have dζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have dG : DifferentiableAt ℂ (fun w : ℂ => Gamma (w / 2)) s := by
    have : DifferentiableAt ℂ Gamma (s / 2) :=
      differentiableAt_Gamma _ hne
    exact this.comp s (differentiableAt_id.div_const 2)
  have dP : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact h.const_cpow (Or.inl hπ)
  have hev : riemannXi =ᶠ[nhds s] fun w => (1 / 2 : ℂ) *
      (w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)))) := by
    have ho : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [ho.mem_nhds hs] with w hw
    have hw' : (1:ℝ) < w.re := hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw'; linarith
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw'
    have hGw : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_mul_completedRiemannZeta hw0 hw1, riemannZeta_def_of_ne_zero hw0]
    have hGw' : Gamma (w / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      simp; linarith
    have hPw : (Real.pi : ℂ) ^ (-w / 2) ≠ 0 := by
      simp [hπ]
    rw [Gammaℝ_def]
    field_simp
  have e1 : logDeriv riemannXi s = logDeriv (fun w => (1 / 2 : ℂ) *
      (w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))))) s := by
    simp only [logDeriv_apply]
    rw [hev.deriv_eq, hev.eq_of_nhds]
  have lG : logDeriv (fun w : ℂ => Gamma (w / 2)) s = digamma (s / 2) / 2 := by
    have := logDeriv_comp (f := Gamma) (g := fun w : ℂ => w / 2) (x := s)
      (differentiableAt_Gamma _ hne) (differentiableAt_id.div_const 2)
    rw [show (Gamma ∘ fun w : ℂ => w / 2) = fun w : ℂ => Gamma (w / 2) from rfl] at this
    rw [this, digamma_def]
    simp [div_eq_mul_inv]
  have lP : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply, dP.deriv, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have d1 : DifferentiableAt ℂ (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s := dG.mul dζ
  have d2 : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s :=
    dP.differentiableAt.mul d1
  have d3 : DifferentiableAt ℂ
      (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s :=
    (differentiableAt_fun_id.sub_const 1).mul d2
  have lid : logDeriv (fun w : ℂ => w) s = 1 / s := logDeriv_id s
  have lsub : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    simp
  have n1 : Gamma (s / 2) * riemannZeta s ≠ 0 := mul_ne_zero hG hζ
  have n2 : (Real.pi : ℂ) ^ (-s / 2) * (Gamma (s / 2) * riemannZeta s) ≠ 0 := mul_ne_zero hP n1
  have n3 : (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * (Gamma (s / 2) * riemannZeta s)) ≠ 0 :=
    mul_ne_zero hs1' n2
  have m1 : logDeriv (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s =
      logDeriv (fun w : ℂ => Gamma (w / 2)) s + logDeriv riemannZeta s :=
    logDeriv_fun_mul s hG hζ dG dζ
  have m2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s =
      logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s +
        logDeriv (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s :=
    logDeriv_fun_mul s hP n1 dP.differentiableAt d1
  have m3 : logDeriv
      (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s =
      logDeriv (fun w : ℂ => w - 1) s +
        logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s :=
    logDeriv_fun_mul s hs1' n2 (differentiableAt_fun_id.sub_const 1) d2
  have m4 : logDeriv (fun w : ℂ =>
      w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)))) s =
      logDeriv (fun w : ℂ => w) s + logDeriv
        (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s :=
    logDeriv_fun_mul s hs0 n3 differentiableAt_fun_id d3
  rw [e1, logDeriv_const_mul _ _ (by norm_num), m4, m3, m2, m1, lG, lP, lid, lsub]
  ring

/-- `2 + γ - log(4π) = 0.0461…`. -/
theorem two_add_eulerMascheroni_sub_log_four_pi_lt :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
  have hγ : Real.eulerMascheroniConstant < 61244/10000 - 8 * Real.log 2 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
    have e : Real.eulerMascheroniSeq' 256 = (harmonic 256 : ℝ) - Real.log 256 := by
      simp only [Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat]
    have l : Real.log (256:ℝ) = 8 * Real.log 2 := by
      rw [show (256:ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have c : (harmonic 256 : ℝ) ≤ 61244/10000 := by
      have := (Rat.cast_le (K := ℝ)).2 harmonic_256_le
      push_cast at this
      exact this
    linarith
  have hπ : 33 * Real.log 2 + (1 - 1/(102/100:ℝ)) ≤ 20 * Real.log Real.pi := by
    have h1 : (1 - 1/(102/100:ℝ)) ≤ Real.log (102/100) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 102/100 by norm_num)
      simpa using this
    have h2 : (2:ℝ)^33 * (102/100) ≤ Real.pi ^ 20 := by
      have : (3.1415:ℝ)^20 ≤ Real.pi ^ 20 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 20
      refine le_trans ?_ this
      norm_num
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h3
    push_cast at h3
    linarith
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  rw [h4]
  norm_num at hπ
  linarith

end SchoenfeldRH
