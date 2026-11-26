import SchoenfeldRH.Xi.Basic
import SchoenfeldRH.Xi.Hadamard
import SchoenfeldRH.Xi.LogDeriv

/-!
# The facts about `ξ` in the form in which the rest of the proof uses them

Restatements of the theorems of `SchoenfeldRH/Xi/{Basic,Hadamard,LogDeriv}.lean` with `logDeriv f s` written out
as `deriv f s / f s`.
-/

open Complex

namespace SchoenfeldRH

/-- The constant `c = ξ'/ξ(1) = 1 + γ/2 - log(4π)/2`. -/
noncomputable def xiConst : ℝ := 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2

theorem riemannXi_zero_re_mem {ρ : ℂ} (h : riemannXi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  riemannXi_eq_zero_re h

theorem deriv_div_riemannXi_one : deriv riemannXi 1 / riemannXi 1 = (xiConst : ℂ) := by
  rw [← logDeriv_apply]; exact logDeriv_riemannXi_one

theorem deriv_div_riemannXi_zero : deriv riemannXi 0 / riemannXi 0 = -(xiConst : ℂ) := by
  rw [← logDeriv_apply]; exact logDeriv_riemannXi_zero

theorem hasSum_hadamard_riemannXi {s : ℂ} (hs : riemannXi s ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (deriv riemannXi s / riemannXi s + (xiConst : ℂ)) := by
  have h := hasSum_logDeriv_riemannXi hs
  rwa [logDeriv_apply, logDeriv_apply, deriv_div_riemannXi_zero, sub_neg_eq_add] at h

theorem logDeriv_riemannZeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannXi s / riemannXi s - 1 / s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2
        - digamma (s / 2) / 2 := by
  have h := logDeriv_riemannZeta_eq_logDeriv_riemannXi hs
  rwa [logDeriv_apply, logDeriv_apply] at h

theorem two_mul_xiConst_lt : 2 * xiConst < 1 / 20 := by
  have := two_add_eulerMascheroni_sub_log_four_pi_lt
  unfold xiConst
  linarith

end SchoenfeldRH
