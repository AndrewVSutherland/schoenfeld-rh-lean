import SchoenfeldRH.Xi.Compat
import SchoenfeldRH.Lemmas.p4.DigammaAux

/-!
# An upper bound for `ξ'/ξ` on the real axis

One estimate, used by `SchoenfeldRH.ZeroSum.Bound`.
-/

namespace SchoenfeldRH

open Complex

/-- The real part of `L(Λ, x)` is nonnegative at a real point. -/
private lemma p9_re_LSeries_vonMangoldt_nonneg (x : ℝ) :
    0 ≤ (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (x : ℂ)).re := by
  open scoped ComplexOrder in
  have h : 0 ≤ LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (x : ℂ) := by
    unfold LSeries
    refine tsum_nonneg fun n => LSeries.term_nonneg ?_ x
    exact Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg
  exact (Complex.nonneg_iff.mp h).1

/-- Elementary inequality. -/
private lemma p9_rat_ineq {β : ℝ} (hβ : 5 / 2 ≤ β) :
    1 / (β + 1 / 2) + 1 / (β - 1 / 2) + 1 / (4 * β) ≤ 7 / 3 / β := by
  have hb : 0 < β := by linarith
  have h1 : 0 < β - 1 / 2 := by linarith
  have h2 : 0 < β + 1 / 2 := by linarith
  have h3 : (2 : ℝ) * β - 1 ≠ 0 := (by linarith : (0 : ℝ) < 2 * β - 1).ne'
  have h4 : (-1 : ℝ) + β * 2 ≠ 0 := (by linarith : (0 : ℝ) < -1 + β * 2).ne'
  have h5 : (2 : ℝ) * β + 1 ≠ 0 := (by linarith : (0 : ℝ) < 2 * β + 1).ne'
  have heq : 7 / 3 / β - (1 / (β + 1 / 2) + 1 / (β - 1 / 2) + 1 / (4 * β)) =
      (β ^ 2 - 25 / 4) / (12 * β * ((β + 1 / 2) * (β - 1 / 2))) := by
    have n1 := h1.ne'
    have n2 := h2.ne'
    have n12 : (β + 1 / 2) * (β - 1 / 2) ≠ 0 := mul_ne_zero n2 n1
    have n4 : (4 : ℝ) * β ≠ 0 := by positivity
    have n3 : (3 : ℝ) * β ≠ 0 := by positivity
    have nd : (β + 1 / 2) * (β - 1 / 2) * (4 * β) ≠ 0 := mul_ne_zero n12 n4
    have nr : 12 * β * ((β + 1 / 2) * (β - 1 / 2)) ≠ 0 := mul_ne_zero (by positivity) n12
    rw [div_add_div _ _ n2 n1, div_add_div _ _ n12 n4, div_div, div_sub_div _ _ n3 nd,
      div_eq_div_iff (mul_ne_zero n3 nd) nr]
    ring
  have hnum : 0 ≤ β ^ 2 - 25 / 4 := by nlinarith
  have : 0 ≤ (β ^ 2 - 25 / 4) / (12 * β * ((β + 1 / 2) * (β - 1 / 2))) := by positivity
  linarith

/-- `Re ξ'/ξ(β + 1/2) ≤ ½ log(β/2π) + (7/3)/β` for real `β ≥ 5/2`. -/
theorem re_logDeriv_riemannXi_le {β : ℝ} (hβ : 5 / 2 ≤ β) :
    (deriv riemannXi ((β + 1 / 2 : ℝ) : ℂ) / riemannXi ((β + 1 / 2 : ℝ) : ℂ)).re
      ≤ Real.log (β / (2 * Real.pi)) / 2 + 7 / 3 / β := by
  set s : ℂ := ((β + 1 / 2 : ℝ) : ℂ) with hs_def
  have hs : 1 < s.re := by rw [hs_def, Complex.ofReal_re]; linarith
  have key := logDeriv_riemannZeta_eq hs
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  set L := LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s with hL_def
  have hLnn : 0 ≤ L.re := p9_re_LSeries_vonMangoldt_nonneg (β + 1 / 2)
  have hxpos : 0 < (β + 1 / 2) / 2 := by linarith
  have hhalf : s / 2 = (((β + 1 / 2) / 2 : ℝ) : ℂ) := by rw [hs_def]; push_cast; ring
  set d : ℝ := deriv Real.Gamma ((β + 1 / 2) / 2) / Real.Gamma ((β + 1 / 2) / 2) with hd_def
  have hψ : Complex.digamma (s / 2) = (d : ℂ) := by
    rw [hhalf]; exact P4.digamma_ofReal_eq hxpos
  have hξ : deriv riemannXi s / riemannXi s = -L +
      ((1 / (β + 1 / 2) + 1 / (β - 1 / 2) - 1 / 2 * Real.log Real.pi
        + 1 / 2 * d : ℝ) : ℂ) := by
    have e : deriv riemannXi s / riemannXi s = -L + 1 / s + 1 / (s - 1) +
        (-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 * Complex.digamma (s / 2)) := by
      linear_combination (-1 : ℂ) * key + hL
    rw [e, hψ, hs_def]
    push_cast
    ring_nf
  rw [hξ, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  have hψle : d ≤ Real.log ((β + 1 / 2) / 2) := (P4.bounds (x := (β + 1 / 2) / 2) (by linarith)).2
  have hb : 0 < β := by linarith
  have hpi := Real.pi_pos
  have hlog1 : Real.log ((β + 1 / 2) / 2) = Real.log (β + 1 / 2) - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hlog2 : Real.log (β / (2 * Real.pi)) = Real.log β - (Real.log 2 + Real.log Real.pi) := by
    rw [Real.log_div hb.ne' (by positivity), Real.log_mul (by norm_num) hpi.ne']
  have hlog3 : Real.log ((β + 1 / 2) / β) = Real.log (β + 1 / 2) - Real.log β :=
    Real.log_div (by linarith) hb.ne'
  have hlog4 : Real.log ((β + 1 / 2) / β) ≤ (β + 1 / 2) / β - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : (β + 1 / 2) / β - 1 = 1 / (2 * β) := by field_simp; ring
  have hrat := p9_rat_ineq hβ
  have h4 : 1 / (2 * β) / 2 = 1 / (4 * β) := by field_simp; ring
  nlinarith [hψle, hlog1, hlog2, hlog3, hlog4, hfrac, hrat, h4]

end SchoenfeldRH
-- stamp: 3
