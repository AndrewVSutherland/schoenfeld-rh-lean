import SchoenfeldRH.Explicit.Formula

/-!
# The two `ψ` inequalities under the Riemann hypothesis (Contract E)

For natural `x ≥ 2` and real `λ > 2`, under RH, with `W = zeroSumW`:

* `psi_sub_le_of_RH`:  `ψ(x) − x ≤ x/(λ−1) + √x · λ W(λ − 1/2) + 3`;
* `sub_psi_le_of_RH`:  `x − ψ(x) ≤ x/(λ+1) + (√x + 1) · λ W(λ + 1/2) + 3`  (`λ` not an even integer).

Both follow from the smoothed explicit formula `Explicit.explicit_formula_mu`:

* lower bound for `ψ`: `ψ(x) ≥ Σ_{n ≤ x} Λ(n)(1 − (n/x)^λ)`, formula with `μ = λ`; the sum over the trivial
  zeros has a sign, the constant is `−log 2π ∈ [−2, 0]`;
* upper bound for `ψ`: `ψ(x) ≤ Σ_{n ≤ x} Λ(n)(1 − (x/n)^λ) + x^λ Σ_{n ≥ 1} Λ(n) n^(−λ)`, formula with `μ = −λ`
  plus the partial-fraction expansion of `−ζ'/ζ` at `s = λ` (`Explicit.neg_logDeriv_zeta_eq`), which
  cancels all terms carrying `x^λ`:
  `ψ(x) ≤ λx/(λ−1) − log 2π − Σ_ρ m_ρ λ x^ρ/(ρ(λ−ρ)) − Σ_k λ x^(−2k)/((−2k)(λ+2k))`.
-/

open Complex ArithmeticFunction

namespace SchoenfeldRH

open Explicit

namespace Explicit

/-- `pairE` at a real point is real. -/
lemma pairE_ofReal {x : ℝ} (hx : 0 < x) (μ r : ℝ) :
    pairE x μ (r : ℂ) = ((μ * (x ^ r - x ^ (-μ)) / (r * (r + μ)) : ℝ) : ℂ) := by
  unfold pairE
  rw [← ofReal_neg, ← ofReal_cpow hx.le, ← ofReal_cpow hx.le]
  push_cast
  ring

lemma trivZero_eq_ofReal (k : ℕ) : trivZero k = ((-(2 * ((k : ℝ) + 1)) : ℝ) : ℂ) := by
  simp [trivZero]

/-- The term `n = x` does not contribute to the smoothed sum. -/
lemma sum_Ioo_eq_sum_Ioc (x : ℕ) (hx : 1 ≤ x) (μ : ℝ) :
    ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ)
      = ∑ n ∈ Finset.Ioc 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) := by
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  rw [← Finset.Ioo_insert_right (show 0 < x by omega), Finset.sum_insert (by simp)]
  simp [div_self hx0]

/-- A sum over the zeros is bounded by `zeroSumW` if its terms are. -/
lemma norm_tsum_zero_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 0 < B) (C : ℝ)
    (f : {ρ : ℂ // riemannXi ρ = 0} → ℂ)
    (hf : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, ‖f ρ‖ ≤ C * ((analyticOrderNatAt riemannXi ρ : ℝ) /
      (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖))) :
    ‖∑' ρ, f ρ‖ ≤ C * zeroSumW B := by
  have hsW := (summable_zeroSumW hRH B hB).mul_left C
  have hsn : Summable (fun ρ => ‖f ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf hsW
  calc ‖∑' ρ, f ρ‖ ≤ ∑' ρ, ‖f ρ‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, C * ((analyticOrderNatAt riemannXi ρ : ℝ) /
          (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)) := hsn.tsum_le_tsum hf hsW
    _ = C * zeroSumW B := by rw [tsum_mul_left]; rfl

lemma log_two_pi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.pi_lt_d2
  rw [h2]
  nlinarith

end Explicit

/-- Contract E, lower bound for `ψ`: under RH, for natural `x ≥ 2` and real `λ > 2` not an even
integer, `x − ψ(x) ≤ x/(λ+1) + (√x + 1) λ W(λ + 1/2) + 3`. -/
theorem sub_psi_le_of_RH (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) (lam : ℝ) (hlam : 2 < lam)
    (hne : ∀ k : ℕ, lam ≠ 2 * k) :
    x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * zeroSumW (lam + 1 / 2)) + 3 := by
  have hX : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hX0 : (0 : ℝ) < x := by linarith
  have hl0 : 0 ≤ lam := by linarith
  have hne' : ∀ k : ℕ, trivZero k + (lam : ℂ) ≠ 0 := by
    intro k h
    apply hne (k + 1)
    have := congrArg re h
    rw [add_re, trivZero_re, ofReal_re, zero_re] at this
    push_cast
    linarith
  obtain ⟨hZs, hTs, hE⟩ := explicit_formula_mu x (by omega) lam (Or.inl (by linarith)) hne'
  set S : ℝ := ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ lam) with hS
  set Z : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x lam ρ
    with hZdef
  set T : ℂ := ∑' k : ℕ, pairE x lam (trivZero k) with hTdef
  /- real parts -/
  have h1 : pairE x lam 1 = ((lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam) : ℝ) : ℂ) := by
    have := pairE_ofReal hX0 lam 1
    rw [ofReal_one] at this
    rw [this, Real.rpow_one, one_mul]
  have hre : S = lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam)
      - Real.log (2 * Real.pi) * (1 - (x : ℝ) ^ (-lam)) - Z.re - T.re := by
    rw [h1, ← ofReal_mul, ← ofReal_sub] at hE
    have := congrArg re hE
    simpa only [sub_re, ofReal_re] using this
  /- the trivial zeros -/
  have hT : T.re ≤ 0 := by
    rw [hTdef, Complex.re_tsum hTs]
    refine tsum_nonpos fun k => ?_
    rw [trivZero_eq_ofReal, pairE_ofReal hX0, ofReal_re]
    set r : ℝ := -(2 * ((k : ℝ) + 1)) with hr_def
    have hr : r < 0 := by rw [hr_def]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    have hrl : r + lam ≠ 0 := by
      intro h
      apply hne (k + 1)
      push_cast
      rw [hr_def] at h
      linarith
    have hq : 0 ≤ ((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r + lam) := by
      rcases lt_or_gt_of_ne hrl with h | h
      · exact div_nonneg_of_nonpos
          (sub_nonpos.2 (Real.rpow_le_rpow_of_exponent_le hX (by linarith))) h.le
      · exact div_nonneg (sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hX (by linarith))) h.le
    have e : lam * ((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r * (r + lam))
        = (lam / r) * (((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r + lam)) := by
      field_simp
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos hl0 hr.le) hq
  /- the zeros -/
  have hZ : ‖Z‖ ≤ lam * (Real.sqrt x + 1) * zeroSumW (lam + 1 / 2) := by
    refine norm_tsum_zero_le hRH (by linarith) _ _ fun ρ => ?_
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    have hnum : ‖((x : ℝ) : ℂ) ^ (ρ : ℂ) - ((x : ℝ) : ℂ) ^ (-(lam : ℂ))‖ ≤ Real.sqrt x + 1 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_cpow_eq_rpow_re_of_pos hX0, hρ, Real.sqrt_eq_rpow]
      · rw [norm_cpow_eq_rpow_re_of_pos hX0, neg_re, ofReal_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
    have hden : ‖(ρ : ℂ) + lam‖ = ‖(((lam + 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ)‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        normSq_apply, normSq_apply]
      simp [hρ]
      ring
    unfold pairE
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl0, hden]
    calc _ ≤ (analyticOrderNatAt riemannXi ρ : ℝ) * (lam * (Real.sqrt x + 1) /
          (‖(ρ : ℂ)‖ * ‖(((lam + 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ)‖)) := by gcongr
      _ = _ := by ring
  /- conclusion -/
  have hψ : S ≤ Chebyshev.psi x := by
    rw [hS, sum_Ioo_eq_sum_Ioc x (by omega), Chebyshev.psi, Nat.floor_natCast]
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 : 0 ≤ ((n : ℝ) / x) ^ lam := by positivity
    have h2 : 0 ≤ (Λ n : ℝ) := vonMangoldt_nonneg
    nlinarith
  have hxl0 : 0 ≤ (x : ℝ) ^ (-lam) := by positivity
  have hxl1 : (x : ℝ) ^ (-lam) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  have hlog0 := log_two_pi_nonneg
  have hlog2 := log_two_pi_le_two
  have hZre : Z.re ≤ ‖Z‖ := re_le_norm Z
  have e1 : (x : ℝ) - lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam)
      = x / (lam + 1) + lam / (1 + lam) * (x : ℝ) ^ (-lam) := by
    field_simp
    ring
  have e2 : lam / (1 + lam) * (x : ℝ) ^ (-lam) ≤ 1 := by
    have : lam / (1 + lam) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h0 : 0 ≤ lam / (1 + lam) := by positivity
    nlinarith
  have e3 : Real.log (2 * Real.pi) * (1 - (x : ℝ) ^ (-lam)) ≤ 2 := by nlinarith
  have e4 : (Real.sqrt x + 1) * (lam * zeroSumW (lam + 1 / 2))
      = lam * (Real.sqrt x + 1) * zeroSumW (lam + 1 / 2) := by ring
  linarith

/-- Contract E, upper bound for `ψ`: under RH, for natural `x ≥ 2` and real `λ > 2`,
`ψ(x) − x ≤ x/(λ−1) + √x λ W(λ − 1/2) + 3`. -/
theorem psi_sub_le_of_RH (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) (lam : ℝ) (hlam : 2 < lam) :
    Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * zeroSumW (lam - 1 / 2)) + 3 := by
  have hX2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hX : (1 : ℝ) ≤ x := by linarith
  have hX0 : (0 : ℝ) < x := by linarith
  have hl0 : 0 ≤ lam := by linarith
  have hne' : ∀ k : ℕ, trivZero k + ((-lam : ℝ) : ℂ) ≠ 0 := by
    intro k h
    have := congrArg re h
    rw [add_re, trivZero_re, ofReal_re, zero_re] at this
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  obtain ⟨hZs, hTs, hE⟩ := explicit_formula_mu x (by omega) (-lam) (Or.inr (by linarith)) hne'
  set S : ℝ := ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ (-lam)) with hS
  /- the expansion of `-ζ'/ζ` at `s = λ` -/
  have hs : 1 < ((lam : ℝ) : ℂ).re := by rw [ofReal_re]; linarith
  have hξ : riemannXi (lam : ℂ) ≠ 0 := fun h => by linarith [(riemannXi_zero_re_mem h).2]
  have hPZ := (hasSum_hadamard_riemannXi hξ).summable.hasSum
  have hPT := (hasSum_trivZero (s := (lam : ℂ)) (by rw [ofReal_re]; linarith)).summable.hasSum
  have hL := neg_logDeriv_zeta_eq hs
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have hLS : LSeries a lam = -(deriv riemannZeta lam / riemannZeta lam) := by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    change LSeries a lam = _ at h1
    rw [h1, neg_div]
  set XL : ℂ := (((x : ℝ) ^ lam : ℝ) : ℂ) with hXL
  set Q : ℂ → ℂ := fun w => lam * ((x : ℝ) : ℂ) ^ w / (w * (lam - w)) with hQdef
  have hQ : ∀ w : ℂ, w ≠ 0 → (lam : ℂ) - w ≠ 0 →
      pairE x (-lam) w + XL * (1 / (lam - w) + 1 / w) = Q w := by
    intro w hw0 hwl
    have e : ((x : ℝ) : ℂ) ^ (-(((-lam : ℝ)) : ℂ)) = XL := by
      rw [hXL, ofReal_cpow hX0.le, ofReal_neg, neg_neg]
    have hwl' : w + -(lam : ℂ) ≠ 0 := fun h => hwl (by linear_combination -h)
    have hwl'' : w - (lam : ℂ) ≠ 0 := fun h => hwl (by linear_combination -h)
    unfold pairE
    rw [e]
    simp only [hQdef, ofReal_neg]
    field_simp
    ring
  set Z : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
    (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x (-lam) ρ with hZdef
  set T : ℂ := ∑' k : ℕ, pairE x (-lam) (trivZero k) with hTdef
  have hρre : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, (lam : ℂ) - (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re] at this
    linarith [(riemannXi_zero_re_mem ρ.2).2]
  have hkre : ∀ k : ℕ, (lam : ℂ) - trivZero k ≠ 0 := fun k h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re, trivZero_re] at this
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hZQ : HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
      (Z + XL * ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((lam : ℂ) - ρ) + 1 / ρ)) := by
    have := hZs.hasSum.add (hPZ.mul_left XL)
    have key : (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
        = fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x (-lam) ρ
          + XL * ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((lam : ℂ) - ρ) + 1 / ρ)) :=
      funext fun ρ => by rw [← hQ ρ (riemannXi_zero_ne_zero ρ.2) (hρre ρ)]; ring
    rw [key]
    exact this
  have hTQ : HasSum (fun k : ℕ => Q (trivZero k))
      (T + XL * ∑' k : ℕ, (1 / ((lam : ℂ) - trivZero k) + 1 / trivZero k)) := by
    have := hTs.hasSum.add (hPT.mul_left XL)
    have key : (fun k : ℕ => Q (trivZero k))
        = fun k => pairE x (-lam) (trivZero k)
          + XL * (1 / ((lam : ℂ) - trivZero k) + 1 / trivZero k) :=
      funext fun k => (hQ _ (trivZero_ne_zero k) (hkre k)).symm
    rw [key]
    exact this
  have h1l : (lam : ℂ) - 1 ≠ 0 := fun h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re, one_re] at this
    linarith
  have hmain : (S : ℂ) + XL * LSeries a lam
      = Q 1 - (Real.log (2 * Real.pi) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
        - ∑' k : ℕ, Q (trivZero k) := by
    have e1 : ((1 - (x : ℝ) ^ (-(-lam)) : ℝ) : ℂ) = 1 - XL := by
      rw [hXL, neg_neg]; push_cast; ring
    rw [hZQ.tsum_eq, hTQ.tsum_eq, ← hQ 1 one_ne_zero h1l, hE, e1, hLS, hL]
    ring
  /- real parts -/
  set ZQ : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ with hZQdef
  set TQ : ℂ := ∑' k : ℕ, Q (trivZero k) with hTQdef
  set Lre : ℝ := (LSeries a lam).re with hLre
  have hQ1 : Q 1 = ((lam * x / (lam - 1) : ℝ) : ℂ) := by
    simp only [hQdef, cpow_one]
    push_cast
    ring
  have hre : S + (x : ℝ) ^ lam * Lre
      = lam * x / (lam - 1) - Real.log (2 * Real.pi) - ZQ.re - TQ.re := by
    have hXLre : (XL * LSeries a lam).re = (x : ℝ) ^ lam * Lre := by rw [hXL, re_ofReal_mul]
    have := congrArg re hmain
    rw [hQ1, ← ofReal_sub] at this
    simp only [add_re, sub_re, ofReal_re, hXLre] at this
    exact this
  /- the Dirichlet series at `λ` dominates its partial sums -/
  have hterm : ∀ n : ℕ, (LSeries.term a lam n).re
      = if n = 0 then 0 else (Λ n : ℝ) / (n : ℝ) ^ lam := by
    intro n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp
    · have : (n : ℂ) ^ (lam : ℂ) = (((n : ℝ) ^ lam : ℝ) : ℂ) := by
        rw [ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
      rw [this, ← ofReal_div, ofReal_re]
  have hsumL : HasSum (fun n : ℕ => (LSeries.term a lam n).re) Lre := by
    have hsm : Summable (LSeries.term a lam) := LSeriesSummable_vonMangoldt hs
    have := Complex.reCLM.hasSum hsm.hasSum
    simp only [Complex.reCLM_apply] at this
    exact this
  have hterm0 : ∀ n : ℕ, 0 ≤ (LSeries.term a lam n).re := by
    intro n
    rw [hterm]
    split_ifs
    · exact le_rfl
    · exact div_nonneg vonMangoldt_nonneg (by positivity)
  have hpart : ∑ n ∈ Finset.Ioc 0 x, (LSeries.term a lam n).re ≤ Lre :=
    sum_le_hasSum _ (fun n _ => hterm0 n) hsumL
  have hxl : (0 : ℝ) < (x : ℝ) ^ lam := by positivity
  have hψ : Chebyshev.psi x ≤ S + (x : ℝ) ^ lam * Lre := by
    have e : Chebyshev.psi x = S + (x : ℝ) ^ lam * ∑ n ∈ Finset.Ioc 0 x, (LSeries.term a lam n).re := by
      rw [hS, sum_Ioo_eq_sum_Ioc x (by omega), Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      have hn0 : n ≠ 0 := by omega
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      have hnl : (0 : ℝ) < (n : ℝ) ^ lam := by positivity
      rw [hterm]
      simp only [hn0, ↓reduceIte]
      rw [Real.rpow_neg (by positivity), Real.div_rpow hnpos.le hX0.le]
      field_simp
      ring
    rw [e]
    gcongr
  /- the zeros -/
  have hZ : ‖ZQ‖ ≤ lam * Real.sqrt x * zeroSumW (lam - 1 / 2) := by
    refine norm_tsum_zero_le hRH (by linarith) _ _ fun ρ => ?_
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    have hnum : ‖((x : ℝ) : ℂ) ^ (ρ : ℂ)‖ = Real.sqrt x := by
      rw [norm_cpow_eq_rpow_re_of_pos hX0, hρ, Real.sqrt_eq_rpow]
    have hden : (lam : ℂ) - (ρ : ℂ) = (((lam - 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ) := by
      push_cast; ring
    simp only [hQdef]
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl0, hnum, hden]
    apply le_of_eq
    ring
  /- the trivial zeros -/
  have hT : -(1 / 3 : ℝ) ≤ TQ.re := by
    have hg : HasSum (fun k : ℕ => -(1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k) (-(1 / 4 : ℝ) * (1 - 1 / 4)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hq : HasSum (fun k : ℕ => (Q (trivZero k)).re) TQ.re := by
      have := Complex.reCLM.hasSum hTQ.summable.hasSum
      simpa only [Complex.reCLM_apply] using this
    have hQreal : ∀ r : ℝ, Q (r : ℂ) = ((lam * (x : ℝ) ^ r / (r * (lam - r)) : ℝ) : ℂ) := by
      intro r
      simp only [hQdef]
      rw [← ofReal_cpow hX0.le]
      push_cast
      ring
    have hle : ∀ k : ℕ, -(1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k ≤ (Q (trivZero k)).re := by
      intro k
      rw [trivZero_eq_ofReal, hQreal, ofReal_re]
      set r : ℝ := -(2 * ((k : ℝ) + 1)) with hr_def
      have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have hr : r ≤ -2 := by rw [hr_def]; linarith
      have h2r : (2 : ℝ) ^ r = 1 / 4 * (1 / 4 : ℝ) ^ k := by
        have e : r = -(((2 * (k + 1) : ℕ)) : ℝ) := by rw [hr_def]; push_cast; ring
        rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_mul, ← pow_succ' (1 / 4 : ℝ) k,
          ← inv_pow]
        norm_num
      have hxr : (x : ℝ) ^ r ≤ 1 / 4 * (1 / 4 : ℝ) ^ k := by
        rw [← h2r]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hX2 (by linarith)
      have hxr0 : 0 ≤ (x : ℝ) ^ r := by positivity
      have e : lam * (x : ℝ) ^ r / (r * (lam - r))
          = -((lam / (lam - r)) * (1 / (-r)) * (x : ℝ) ^ r) := by
        have h1 : r ≠ 0 := by linarith
        have h2 : lam - r ≠ 0 := by linarith
        field_simp
      rw [e, neg_mul, neg_le_neg_iff]
      have hA : lam / (lam - r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hA0 : 0 ≤ lam / (lam - r) := div_nonneg hl0 (by linarith)
      have hB : 1 / (-r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hB0 : 0 ≤ 1 / (-r) := div_nonneg zero_le_one (by linarith)
      calc lam / (lam - r) * (1 / (-r)) * (x : ℝ) ^ r ≤ 1 * 1 * (1 / 4 * (1 / 4 : ℝ) ^ k) := by
            gcongr
        _ = _ := by ring
    have := hasSum_le hle hg hq
    norm_num at this
    linarith
  /- conclusion -/
  have hlog0 := log_two_pi_nonneg
  have hZre : -ZQ.re ≤ ‖ZQ‖ := by
    have := abs_re_le_norm ZQ
    linarith [neg_abs_le ZQ.re]
  have e1 : lam * (x : ℝ) / (lam - 1) - x = x / (lam - 1) := by
    have : lam - 1 ≠ 0 := by linarith
    field_simp
    ring
  have e4 : Real.sqrt x * (lam * zeroSumW (lam - 1 / 2))
      = lam * Real.sqrt x * zeroSumW (lam - 1 / 2) := by ring
  linarith

end SchoenfeldRH
