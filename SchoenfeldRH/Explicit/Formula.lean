import SchoenfeldRH.Explicit.Weighted
import SchoenfeldRH.Explicit.LogDeriv
import SchoenfeldRH.Lemmas.p8.TsumIntegrable

/-!
# The smoothed explicit formula with kernel `μ x^s / (s (s + μ))`

-/

open Complex MeasureTheory ArithmeticFunction

namespace SchoenfeldRH.Explicit

theorem explicit_formula_mu (x : ℕ) (hx : 1 ≤ x) (μ : ℝ) (hμ : 0 < μ ∨ μ < -1)
    (hne : ∀ k : ℕ, trivZero k + μ ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ) ∧
    Summable (fun k : ℕ => pairE x μ (trivZero k)) ∧
    (((∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ)) : ℂ)
      = pairE x μ 1 - (Real.log (2 * Real.pi) : ℂ) * ((1 - (x : ℝ) ^ (-μ) : ℝ) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ)
        - ∑' k : ℕ, pairE x μ (trivZero k) := by
  classical
  have : Countable {ρ : ℂ // riemannXi ρ = 0} := countable_riemannXi_zeros
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 + |μ| := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc1 : 1 ≤ c - 1 := by rw [hc_def]; linarith [abs_nonneg μ]
  have hcμ : 1 < c + μ := by
    rcases hμ with h | h
    · rw [hc_def, abs_of_pos h]; linarith
    · rw [hc_def, abs_of_neg (by linarith)]; linarith
  have hcμ0 : 0 < c + μ := by linarith
  have hμ1 : (1 : ℂ) + μ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    rcases hμ with h' | h' <;> linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  obtain ⟨K, hK0, hK⟩ := integral_norm_pairK_le (δ := 1) one_pos
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * (x : ℝ) ^ c * |μ| * (1 + |μ - 1|) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hKw : ∀ w : ℂ, w ≠ 0 → w.re ≤ c - 1 →
      Integrable (pairK x c μ w) ∧ ∫ t : ℝ, ‖pairK x c μ w t‖ ≤ M * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
    intro w hw0 hw
    rw [hM]
    exact hK x c μ hxpos hcμ w hw0 hw
  -- facts about the zeros
  have hρ : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      (ρ : ℂ) ≠ 0 ∧ (ρ : ℂ).re ≤ c - 1 ∧ (ρ : ℂ).re < c ∧ (ρ : ℂ) + μ ≠ 0 := by
    intro ρ
    obtain ⟨h0, h1⟩ := riemannXi_zero_re_mem ρ.2
    refine ⟨riemannXi_zero_ne_zero ρ.2, by linarith, by linarith, ?_⟩
    intro h
    have := congrArg Complex.re h
    simp at this
    rcases hμ with h' | h' <;> linarith
  have hτ : ∀ k : ℕ, trivZero k ≠ 0 ∧ (trivZero k).re ≤ c - 1 ∧ (trivZero k).re < c := by
    intro k
    have hr := trivZero_re k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨trivZero_ne_zero k, ?_, ?_⟩ <;> rw [hr] <;> linarith
  -- the nontrivial zeros
  have hF1int : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      Integrable (fun t => (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) :=
    fun ρ => ((hKw ρ (hρ ρ).1 (hρ ρ).2.1).1).const_mul _
  have hF1norm : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      ∫ t, ‖(analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t‖
        = (analyticOrderNatAt riemannXi ρ : ℝ) * ∫ t, ‖pairK x c μ ρ t‖ := by
    intro ρ
    simp_rw [norm_mul, Complex.norm_natCast]
    exact integral_const_mul _ _
  have hsumH := summable_riemannXi_zeros_rpow (τ := 1 + 1 / 2) (by norm_num)
  have hF1sum : Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      ∫ t, ‖(analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t‖ := by
    refine (hsumH.mul_left M).of_nonneg_of_le
      (fun ρ => integral_nonneg fun t => norm_nonneg _) (fun ρ => ?_)
    rw [hF1norm]
    have h := (hKw ρ (hρ ρ).1 (hρ ρ).2.1).2
    have e : ‖(ρ : ℂ)‖ ^ (-(3 / 2 : ℝ)) = 1 / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) := by
      rw [Real.rpow_neg (norm_nonneg _), one_div]; norm_num
    rw [e] at h
    calc (analyticOrderNatAt riemannXi ρ : ℝ) * ∫ t, ‖pairK x c μ ρ t‖
        ≤ (analyticOrderNatAt riemannXi ρ : ℝ) * (M * (1 / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = M * ((analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) := by ring
  have hS1 := hasSum_integral_of_summable_integral_norm hF1int hF1sum
  have hS1' : HasSum
      (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t, ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) := by
    have := hS1.mul_left (1 / (2 * Real.pi) : ℂ)
    convert this using 1
    funext ρ
    rw [integral_const_mul, integral_pairK x c μ hx1 hc hcμ ρ (hρ ρ).2.2.1 (hρ ρ).1 (hρ ρ).2.2.2]
    field_simp
  have hS1i := SchoenfeldRH.Lemmas.p8.integrable_tsum_of_summable_integral_norm hF1int hF1sum
  -- the trivial zeros
  have hF2int : ∀ k : ℕ, Integrable (fun t => pairK x c μ (trivZero k) t) :=
    fun k => (hKw _ (hτ k).1 (hτ k).2.1).1
  have hsumk : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hF2sum : Summable fun k : ℕ => ∫ t, ‖pairK x c μ (trivZero k) t‖ := by
    refine (hsumk.mul_left M).of_nonneg_of_le
      (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
    refine (hKw _ (hτ k).1 (hτ k).2.1).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [norm_trivZero]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
  have hS2 := hasSum_integral_of_summable_integral_norm hF2int hF2sum
  have hS2' : HasSum (fun k : ℕ => pairE x μ (trivZero k))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t, ∑' k : ℕ, pairK x c μ (trivZero k) t) := by
    have := hS2.mul_left (1 / (2 * Real.pi) : ℂ)
    convert this using 1
    funext k
    rw [integral_pairK x c μ hx1 hc hcμ _ (hτ k).2.2 (hτ k).1 (hne k)]
    field_simp
  have hS2i := SchoenfeldRH.Lemmas.p8.integrable_tsum_of_summable_integral_norm hF2int hF2sum
  refine ⟨hS1'.summable, hS2'.summable, ?_⟩
  -- the pointwise identity on the line
  have hpt : ∀ t : ℝ, LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) *
        ((x : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)))
      = pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t
        - ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t
        - ∑' k : ℕ, pairK x c μ (trivZero k) t := by
    intro t
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; linarith
    have hG : (x : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))
        = Kmu c μ x t := by
      simp only [Kmu, Complex.ofReal_natCast]
    rw [hG, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, neg_div, neg_logDeriv_zeta_eq hre]
    rw [sub_mul, sub_mul, sub_mul, ← tsum_mul_right, ← tsum_mul_right]
    have h1 : (1 / ((c : ℂ) + t * I - 1) + 1 / 1) * Kmu c μ x t = pairK x c μ 1 t :=
      pair_mul_kappa hc hcμ0 (by simp; linarith) one_ne_zero t
    rw [div_one] at h1
    have hρK : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((c : ℂ) + t * I - ρ) + 1 / ρ) * Kmu c μ x t
          = (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t := by
      intro ρ
      rw [mul_assoc]
      exact congrArg _ (pair_mul_kappa hc hcμ0 (hρ ρ).2.2.1 (hρ ρ).1 t)
    have hτK : ∀ k : ℕ, (1 / ((c : ℂ) + t * I - trivZero k) + 1 / trivZero k) * Kmu c μ x t
        = pairK x c μ (trivZero k) t := fun k => pair_mul_kappa hc hcμ0 (hτ k).2.2 (hτ k).1 t
    rw [h1]
    simp only [hρK, hτK]
  have hP := perron_weighted_mu (fun n => (Λ n : ℂ)) c μ hc hcμ ?_ x hx
  swap
  · have := (LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simp; linarith))
    rw [LSeriesSummable, ← summable_norm_iff] at this
    refine this.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · subst hn; simp
    · simp
  simp only [hpt] at hP
  have hA : Integrable (pairK x c μ 1) := (hKw 1 one_ne_zero (by simp; linarith)).1
  have hB : Integrable (fun t => (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t) :=
    (integrable_Kmu hc hcμ hxpos).const_mul _
  have hAB : Integrable (fun t => pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t) :=
    hA.sub hB
  have hABC : Integrable (fun t => pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t
      - ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) :=
    hAB.sub hS1i
  rw [integral_sub hABC hS2i, integral_sub hAB hS1i,
    integral_sub hA hB, integral_const_mul, integral_Kmu _ _ _ hxpos hc hcμ,
    integral_pairK x c μ hx1 hc hcμ 1 (by simp; linarith) one_ne_zero hμ1] at hP
  simp only [hx1, ↓reduceIte] at hP
  rw [hS1'.tsum_eq, hS2'.tsum_eq]
  have hL : ((∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℂ) * ((1 - ((n : ℝ) / x) ^ μ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  rw [hL, hP]
  field_simp

end SchoenfeldRH.Explicit
-- stamp: 4
