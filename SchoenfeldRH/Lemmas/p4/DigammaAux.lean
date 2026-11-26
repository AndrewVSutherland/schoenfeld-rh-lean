import Mathlib

/-!
# Auxiliary lemmas for the digamma function (prover p4)
-/

namespace SchoenfeldRH.P4

open Filter Topology Set

lemma re_ne_neg_nat {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -(m : ℂ) := by
  rintro rfl
  simp at hw
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma real_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) := by
  intro h
  have := (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  linarith

lemma deriv_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hf : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (re_ne_neg_nat (by simpa using hx))
  have hg : HasDerivAt Real.Gamma (deriv Real.Gamma x) x :=
    (Real.differentiableAt_Gamma (real_ne_neg_nat hx)).hasDerivAt
  have h1 := hf.hasDerivAt.comp_ofReal
  have h2 := hg.ofReal_comp
  have h3 : (fun y : ℝ => Complex.Gamma (y : ℂ)) = fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [h3] at h1
  exact h1.unique h2

lemma digamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv Real.Gamma x / Real.Gamma x : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Complex.Gamma_ofReal,
    Complex.ofReal_div]

lemma bounds {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ deriv Real.Gamma x / Real.Gamma x ∧
      deriv Real.Gamma x / Real.Gamma x ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hc := Real.convexOn_log_Gamma
  have hd : HasDerivAt (Real.log ∘ Real.Gamma) (deriv Real.Gamma x / Real.Gamma x) x :=
    ((Real.differentiableAt_Gamma (real_ne_neg_nat hx0)).hasDerivAt).log
      (Real.Gamma_pos_of_pos hx0).ne'
  have hrec : ∀ y : ℝ, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  constructor
  · have h := hc.slope_le_of_hasDerivAt (x := x - 1) (y := x) (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr hx0) (by linarith) hd
    rw [slope_def_field] at h
    have h2 := hrec (x - 1) (by linarith)
    rw [sub_add_cancel] at h2
    rw [h2, show x - (x - 1) = (1:ℝ) by ring, div_one] at h
    linarith
  · have h := hc.le_slope_of_hasDerivAt (x := x) (y := x + 1) (mem_Ioi.mpr hx0)
      (mem_Ioi.mpr (by linarith)) (by linarith) hd
    rw [slope_def_field, hrec x hx0, show x + 1 - x = (1:ℝ) by ring, div_one] at h
    linarith

/-! ### The series -/

lemma add_ne_zero' (k : ℕ) {w : ℂ} (hw : 0 < w.re) : (k : ℂ) + w ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

lemma term_eq (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) = (w - 1) / (((k : ℂ) + 1) * ((k : ℂ) + w)) := by
  have h1 : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
  have h2 := add_ne_zero' k hw
  field_simp
  ring

lemma summable_base : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma summable_u (R : ℝ) : Summable (fun k : ℕ => 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2)) :=
  summable_base.mul_left _

lemma term_norm_le {R : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) (hR : ‖w‖ ≤ R) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  rw [term_eq k (by linarith), norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k:ℝ) + 1 := by
    rw [show (k:ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have e2 : (k:ℝ) + 1 / 2 ≤ ‖(k : ℂ) + w‖ := by
    have := Complex.re_le_norm ((k : ℂ) + w)
    simp at this
    linarith
  have e3 : ‖w - 1‖ ≤ R + 1 := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by simp; linarith
  have hR1 : 0 ≤ R + 1 := by linarith [norm_nonneg w]
  rw [e1]
  calc ‖w - 1‖ / (((k:ℝ) + 1) * ‖(k : ℂ) + w‖)
        ≤ (R + 1) / (((k:ℝ) + 1) * ((k:ℝ) + 1 / 2)) := by
        apply div_le_div₀ hR1 e3 (by positivity)
        exact mul_le_mul_of_nonneg_left e2 (by positivity)
    _ ≤ 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hR1 hk) (by positivity : (0:ℝ) ≤ k + 1)]

lemma summable_term {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) :=
  Summable.of_norm_bounded (summable_u ‖w‖) (fun k => term_norm_le hw le_rfl k)

lemma isOpen_U : IsOpen {w : ℂ | 1 / 2 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

lemma differentiableOn_S :
    DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)))
      {w : ℂ | 1 / 2 < w.re} := by
  intro z hz
  set R := ‖z‖ + 1 with hRdef
  have hV : IsOpen ({w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R) :=
    isOpen_U.inter Metric.isOpen_ball
  have hD := Complex.differentiableOn_tsum_of_summable_norm
    (U := {w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R)
    (F := fun (k : ℕ) (w : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))
    (summable_u R) ?_ hV ?_
  · have hzV : z ∈ {w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R := ⟨hz, by simp [R]⟩
    exact (hD.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  · intro k w hw
    have hre : (1:ℝ) / 2 < w.re := hw.1
    have hne := add_ne_zero' k (w := w) (by linarith)
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hne)
  · intro k w hw
    have hre : (1:ℝ) / 2 < w.re := hw.1
    have hb : ‖w‖ < R := by simpa using hw.2
    exact term_norm_le hre hb.le k

lemma analytic_digamma : AnalyticOnNhd ℂ Complex.digamma {w : ℂ | 1 / 2 < w.re} := by
  have hG : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 1 / 2 < w.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z
      (re_ne_neg_nat (by have h : (1:ℝ) / 2 < z.re := hz; linarith))).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 1 / 2 < w.re} := hG.analyticOnNhd isOpen_U
  have : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact hGa.deriv.div hGa fun z hz =>
    Complex.Gamma_ne_zero_of_re_pos (by have h : (1:ℝ) / 2 < z.re := hz; linarith)

lemma partial_sum (w : ℂ) (hw : 0 < w.re) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) =
      (Complex.digamma w - Complex.digamma 1) +
        (Complex.digamma (1 + N) - Complex.digamma (w + N)) := by
  have e1 : ∀ k : ℕ, 1 / ((k : ℂ) + 1) = (1 + (k : ℂ))⁻¹ := by
    intro k; rw [one_div, add_comm]
  have e2 : ∀ k : ℕ, 1 / ((k : ℂ) + w) = (w + (k : ℂ))⁻¹ := by
    intro k; rw [one_div, add_comm]
  simp_rw [e1, e2]
  rw [Finset.sum_sub_distrib, Complex.digamma_apply_add_nat (re_ne_neg_nat (by simp)) N,
    Complex.digamma_apply_add_nat (re_ne_neg_nat hw) N]
  ring

lemma real_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => deriv Real.Gamma (1 + N) / Real.Gamma (1 + N) -
      deriv Real.Gamma (x + N) / Real.Gamma (x + N)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => -(Real.log ((N:ℝ) + x) - Real.log N)) atTop (𝓝 0) := by
    have := ((Real.tendsto_log_comp_add_sub_log x).comp hN).neg
    rw [neg_zero] at this
    exact this
  have hu : Tendsto (fun N : ℕ => (Real.log ((N:ℝ) + 1) - Real.log N) -
      (Real.log ((N:ℝ) + (x - 1)) - Real.log N)) atTop (𝓝 0) := by
    have := ((Real.tendsto_log_comp_add_sub_log 1).comp hN).sub
      ((Real.tendsto_log_comp_add_sub_log (x - 1)).comp hN)
    rw [sub_zero] at this
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have b1 := (bounds (x := 1 + N) (by linarith)).1
    have b2 := (bounds (x := x + N) (by linarith)).2
    rw [show (1:ℝ) + N - 1 = N by ring] at b1
    have e : Real.log ((N:ℝ) + x) = Real.log (x + N) := by rw [add_comm]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have b1 := (bounds (x := 1 + N) (by linarith)).2
    have b2 := (bounds (x := x + N) (by linarith)).1
    have e1 : Real.log ((N:ℝ) + 1) = Real.log (1 + N) := by rw [add_comm]
    have e2 : Real.log ((N:ℝ) + (x - 1)) = Real.log (x + N - 1) := by ring_nf
    linarith

lemma hasSum_real {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x))
      (Complex.digamma x - Complex.digamma 1) := by
  have hx0 : 0 < x := by linarith
  have hs := summable_term (w := (x:ℂ)) (by simpa using hx)
  have key : Tendsto (fun N : ℕ => Complex.digamma (1 + N) - Complex.digamma ((x:ℂ) + N))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (real_limit hx0)
    rw [Complex.ofReal_zero] at h
    refine h.congr' (Eventually.of_forall fun N => ?_)
    simp only [Function.comp_apply, Complex.ofReal_sub]
    rw [← digamma_ofReal_eq (x := 1 + N) (by positivity),
      ← digamma_ofReal_eq (x := x + N) (by positivity)]
    push_cast
    rfl
  have hlim := (tendsto_const_nhds (x := Complex.digamma x - Complex.digamma 1)).add key
  rw [add_zero] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x))) atTop
      (𝓝 (Complex.digamma x - Complex.digamma 1)) := by
    simp_rw [partial_sum (x:ℂ) (by simpa using hx0)]
    exact hlim
  have := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim'
  rw [← this]
  exact hs.hasSum

theorem hasSum_digamma {w : ℂ} (hw : 1 / 2 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))
      (Complex.digamma w - Complex.digamma 1) := by
  have hU : IsPreconnected {w : ℂ | 1 / 2 < w.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hS := differentiableOn_S.analyticOnNhd isOpen_U
  have hP : AnalyticOnNhd ℂ (fun w => Complex.digamma w - Complex.digamma 1)
      {w : ℂ | 1 / 2 < w.re} :=
    analytic_digamma.sub analyticOnNhd_const
  have h1U : (1:ℂ) ∈ {w : ℂ | 1 / 2 < w.re} := by
    show (1:ℝ) / 2 < (1:ℂ).re
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (1:ℂ),
      (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))) =
        Complex.digamma z - Complex.digamma 1 := by
    let f : ℕ → ℂ := fun n => ((1 + 1 / ((n:ℝ) + 1) : ℝ) : ℂ)
    have hf : Tendsto f atTop (𝓝[≠] (1:ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 : Tendsto (fun n : ℕ => (1 + 1 / ((n:ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h0
        have h1 := (Complex.continuous_ofReal.tendsto 1).comp h0
        rw [Complex.ofReal_one] at h1
        exact h1
      · refine Eventually.of_forall fun n => ?_
        simp only [f, Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [← Complex.ofReal_one, Complex.ofReal_inj]
        have : 0 < 1 / ((n:ℝ) + 1) := by positivity
        intro h
        linarith
    refine hf.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    exact (hasSum_real (x := 1 + 1 / ((n:ℝ) + 1)) (by linarith)).tsum_eq
  have hEq := hS.eqOn_of_preconnected_of_frequently_eq hP hU h1U hfreq
  have e : (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))) =
      Complex.digamma w - Complex.digamma 1 := hEq hw
  rw [← e]
  exact (summable_term hw).hasSum

end SchoenfeldRH.P4

-- stamp: 3
