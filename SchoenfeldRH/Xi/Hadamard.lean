import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# The partial-fraction expansion of `ξ'/ξ` over the zeros of `ξ`

The vendored PrimeNumberTheoremAnd modules prove Hadamard's factorization of `Complex.riemannXi` and the resulting
formula for `logDeriv riemannXi` as a sum over `Complex.Hadamard.divisorZeroIndex₀ riemannXi Set.univ`, an index type
that lists each zero as often as its multiplicity. Here the sums are regrouped over the set of zeros, each zero
weighted by its multiplicity `analyticOrderNatAt riemannXi ρ`.
-/

open Complex

namespace SchoenfeldRH

open Complex.Hadamard in
private lemma toNat_divisor_riemannXi (z : ℂ) :
    Int.toNat (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ) z) =
      analyticOrderNatAt riemannXi z := by
  simp [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi z]

private lemma riemannXi_ne_zero_of_eq_zero {ρ : ℂ} (h : riemannXi ρ = 0) : ρ ≠ 0 := by
  rintro rfl
  rw [riemannXi_zero] at h
  norm_num at h

open Complex.Hadamard in
/-- The zeros listed with multiplicity, regrouped by zero. -/
private noncomputable def zeroIndexEquiv :
    divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ≃
      Σ ρ : {ρ : ℂ // riemannXi ρ = 0}, Fin (analyticOrderNatAt riemannXi ρ) where
  toFun p :=
    ⟨⟨p.1.1, by
        have q : Fin (analyticOrderNatAt riemannXi p.1.1) :=
          Fin.cast (toNat_divisor_riemannXi p.1.1) p.1.2
        exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt q.pos)⟩,
      Fin.cast (toNat_divisor_riemannXi p.1.1) p.1.2⟩
  invFun x :=
    ⟨⟨x.1.1, Fin.cast (toNat_divisor_riemannXi x.1.1).symm x.2⟩,
      riemannXi_ne_zero_of_eq_zero x.1.2⟩
  left_inv := by
    rintro ⟨⟨z, q⟩, hz⟩
    rfl
  right_inv := by
    rintro ⟨⟨z, hz⟩, q⟩
    rfl

open Complex.Hadamard in
private lemma zeroIndexEquiv_symm_val
    (x : Σ ρ : {ρ : ℂ // riemannXi ρ = 0}, Fin (analyticOrderNatAt riemannXi ρ)) :
    divisorZeroIndex₀_val (zeroIndexEquiv.symm x) = x.1.1 := rfl

open Complex.Hadamard in
private lemma ne_divisorZeroIndex₀_val {s : ℂ} (hs : riemannXi s ≠ 0)
    (p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) : s ≠ divisorZeroIndex₀_val p := by
  intro h
  exact hs (h ▸ (zeroIndexEquiv p).1.2)

/-- `Σ_ρ m_ρ / |ρ|^τ` converges for every `τ > 1`. -/
theorem summable_riemannXi_zeros_rpow {τ : ℝ} (hτ : 1 < τ) :
    Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ τ := by
  have hgrowth := riemannXi_entireOfOrderAtMost_one.exists_log_growth
    (τ := (1 + τ) / 2) (by linarith) (by linarith)
  have h1 := Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth
    (f := riemannXi) (ρ := (1 + τ) / 2) (τ := τ) (by linarith) (by linarith)
    differentiable_riemannXi riemannXi_nontrivial hgrowth
  have h2 := (zeroIndexEquiv.symm.summable_iff).2 h1
  have h3 := h2.sigma
  refine h3.congr fun ρ => ?_
  simp only [Function.comp_apply, zeroIndexEquiv_symm_val, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.inv_rpow (norm_nonneg _), div_eq_mul_inv]

/-- `ξ'/ξ(s) - ξ'/ξ(0) = Σ_ρ m_ρ (1/(s - ρ) + 1/ρ)` at every `s` with `ξ(s) ≠ 0`. -/
theorem hasSum_logDeriv_riemannXi {s : ℂ} (hs : riemannXi s ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (logDeriv riemannXi s - logDeriv riemannXi 0) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have h0 : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have es := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac (ne_divisorZeroIndex₀_val hs)
  have e0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac (ne_divisorZeroIndex₀_val h0)
  have hz : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = 0 := by
    have hterm : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p = 0 := fun p => by
      rw [zero_sub, one_div, one_div, inv_neg, neg_add_cancel]
    simp only [hterm, tsum_zero]
  have hP : Polynomial.eval s P.derivative = Polynomial.eval 0 P.derivative := by
    rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
    simp
  have hsum := (summable_riemannXi_logDerivTerms_divisorZeroIndex₀
    (ne_divisorZeroIndex₀_val hs)).hasSum
  have hval : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)) =
      logDeriv riemannXi s - logDeriv riemannXi 0 := by
    rw [es, e0, hz, hP]; ring
  rw [hval] at hsum
  have h2 := (zeroIndexEquiv.symm.hasSum_iff).2 hsum
  have h3 := h2.sigma (fun ρ => hasSum_fintype _)
  refine h3.congr_fun fun ρ => ?_
  simp only [Function.comp_apply, zeroIndexEquiv_symm_val, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end SchoenfeldRH
