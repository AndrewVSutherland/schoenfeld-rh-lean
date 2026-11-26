/-
PROVENANCE (vendored file)
  Source repository : https://github.com/AIOvernight/rh-prime-error
  Commit            : c55887da891944dc9f9cc42de53b2216744e746b
  Original path     : RHPrimeError/Converse.lean
  Licence           : Apache-2.0 (see SchoenfeldRH/Converse/LICENSE, copied from the source repository)
  Toolchain         : Lean v4.35.0 / Mathlib 56a00585, the same as the source repository
  Edits             : this provenance comment was prepended; nothing else.
                      Everything after this comment is byte-identical to the original file.
  No statement, definition, proof or name was changed.
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# A square-root error term for `ψ` implies the Riemann Hypothesis

This file proves the converse of "RH implies `ψ(x) - x = O(x ^ (1 / 2 + ε))`": if the Chebyshev
function satisfies `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`, then the Riemann Hypothesis
(in the form of Mathlib's `RiemannHypothesis`) holds.

## Strategy

Write `E(x) = ψ(x) - x` and `H(s) = ∫ x in Ioi 1, E(x) * x ^ (-s - 1)`.

* For `1 < re s`, Abel summation gives `-ζ'(s) / ζ(s) = L(Λ, s) = s * (1 / (s - 1) + H(s))`.
* Under the hypothesis, `H` is a Mellin transform which converges and is holomorphic on
  `1 / 2 < re s`.
* By the identity theorem on the connected open set `{s | 1 / 2 < re s} \ {1}`, the identity
  `ζ'(s) + ζ(s) * (s * (1 / (s - 1) + H(s))) = 0` holds on this whole set.
* If `ζ(ρ) = 0` with `1 / 2 < re ρ` and `ρ ≠ 1`, comparing orders of vanishing at `ρ` in
  `ζ' = -ζ * K` (the order of `ζ'` is one less than that of `ζ`, the order of `ζ * K` is at least
  that of `ζ`) forces `ζ` to vanish identically near `ρ`, hence on `ℂ \ {1}`, which is absurd.
* Finally the functional equation transfers the zero-free region `1 / 2 < re s` to `re s < 1 / 2`
  (apart from the trivial zeros).

## Main results

* `riemannZeta_ne_zero_of_chebyshev_psi_sub_isBigO`: under the hypothesis, `ζ(s) ≠ 0` for
  `1 / 2 < re s`, `s ≠ 1`.
* `riemannHypothesis_of_forall_riemannZeta_ne_zero`: if `ζ` has no zeros with `1 / 2 < re s`,
  then `RiemannHypothesis` holds.
* `riemannHypothesis_of_chebyshev_psi_sub_isBigO`: the hypothesis implies `RiemannHypothesis`.
-/

open Complex Set MeasureTheory Filter Topology Asymptotics
open ArithmeticFunction (vonMangoldt)
open scoped Real

noncomputable section

namespace RHPrimeError

/-- The error term `ψ(x) - x` of the prime number theorem, cut off to `(1, ∞)` and viewed as a
complex valued function. -/
def psiErrorIndicator : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => ((Chebyshev.psi x - x : ℝ) : ℂ)

/-- The integral `∫ x in Ioi 1, (ψ(x) - x) * x ^ (-s - 1)`, written as a Mellin transform. -/
def psiErrorIntegral (s : ℂ) : ℂ :=
  mellin psiErrorIndicator (-s)

lemma locallyIntegrable_psiErrorIndicator : LocallyIntegrable psiErrorIndicator := by
  have h1 : LocallyIntegrable (fun x : ℝ => Chebyshev.psi x - x) :=
    Chebyshev.psi_mono.locallyIntegrable.sub continuous_id.locallyIntegrable
  have h2 : LocallyIntegrable (fun x : ℝ => ((Chebyshev.psi x - x : ℝ) : ℂ)) := by
    intro x
    obtain ⟨U, hU, hf⟩ := h1 x
    exact ⟨U, hU, hf.ofReal⟩
  exact h2.indicator measurableSet_Ioi

lemma psiErrorIndicator_isBigO_atTop {r : ℝ}
    (h : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] fun x : ℝ => x ^ r) :
    psiErrorIndicator =O[atTop] fun x : ℝ => x ^ r := by
  have h' : (fun x : ℝ => ((Chebyshev.psi x - x : ℝ) : ℂ)) =O[atTop] fun x : ℝ => x ^ r :=
    Complex.isBigO_ofReal_left.2 h
  refine h'.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [psiErrorIndicator, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx)]

lemma psiErrorIndicator_isBigO_nhdsGT_zero (b : ℝ) :
    psiErrorIndicator =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
  have h0 : psiErrorIndicator =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℂ) := by
    have hmem : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hmem] with t ht
    exact indicator_of_notMem (by simpa using le_of_lt ht) _
  exact h0.trans_isBigO (isBigO_zero _ _)

section Hypothesis

variable (h : ∀ ε : ℝ, 0 < ε →
  (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε))

include h

lemma psiErrorIndicator_isBigO_rpow_neg {s : ℂ} (hs : 1 / 2 < s.re) :
    psiErrorIndicator =O[atTop] fun x : ℝ => x ^ (-(-(1 / 2 + (s.re - 1 / 2) / 2))) := by
  simpa only [neg_neg] using psiErrorIndicator_isBigO_atTop (h ((s.re - 1 / 2) / 2) (by linarith))

/-- Under the hypothesis, the Mellin integral defining `psiErrorIntegral` converges absolutely on
the half-plane `1 / 2 < re s`. -/
lemma mellinConvergent_psiErrorIndicator {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent psiErrorIndicator (-s) :=
  mellinConvergent_of_isBigO_rpow (b := -s.re - 1)
    (locallyIntegrable_psiErrorIndicator.locallyIntegrableOn _)
    (psiErrorIndicator_isBigO_rpow_neg h hs) (by rw [neg_re]; linarith)
    (psiErrorIndicator_isBigO_nhdsGT_zero _) (by rw [neg_re]; linarith)

/-- Under the hypothesis, `psiErrorIntegral` is holomorphic on the half-plane `1 / 2 < re s`. -/
lemma differentiableAt_psiErrorIntegral {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ psiErrorIntegral s := by
  have hm : DifferentiableAt ℂ (mellin psiErrorIndicator) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (b := -s.re - 1)
      (locallyIntegrable_psiErrorIndicator.locallyIntegrableOn _)
      (psiErrorIndicator_isBigO_rpow_neg h hs) (by rw [neg_re]; linarith)
      (psiErrorIndicator_isBigO_nhdsGT_zero _) (by rw [neg_re]; linarith)
  exact hm.comp s differentiableAt_id.neg

end Hypothesis

lemma sum_Icc_one_floor_vonMangoldt (t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, vonMangoldt k = Chebyshev.psi t := by
  simp [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]

/-- Abel summation: for `1 < re s`, the Dirichlet series of the von Mangoldt function is
`s * (1 / (s - 1) + ∫ x in Ioi 1, (ψ(x) - x) * x ^ (-s - 1))`, provided the integral converges. -/
lemma LSeries_vonMangoldt_eq_mul_psiErrorIntegral {s : ℂ} (hs : 1 < s.re)
    (hconv : MellinConvergent psiErrorIndicator (-s)) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s = s * (1 / (s - 1) + psiErrorIntegral s) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have h1 : ∑ k ∈ Finset.Icc 1 n, vonMangoldt k = Chebyshev.psi n := by
      simpa using sum_Icc_one_floor_vonMangoldt (n : ℝ)
    rw [h1, Real.norm_of_nonneg (Chebyshev.psi_nonneg _), Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  rw [LSeries_eq_mul_integral_of_nonneg (fun n => vonMangoldt n) zero_le_one hs hO
    fun n => ArithmeticFunction.vonMangoldt_nonneg]
  congr 1
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • psiErrorIndicator t) (Ioi 1) :=
    hconv.mono_set (Ioi_subset_Ioi zero_le_one)
  have hcongr : ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (-s) + (t : ℂ) ^ (-s - 1) • psiErrorIndicator t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, cpow_add _ _ htC, cpow_one, mul_comm]
    have hsum : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ) = (Chebyshev.psi t : ℂ) := by
      rw [← sum_Icc_one_floor_vonMangoldt, ofReal_sum]
    simp only [psiErrorIndicator, indicator_of_mem ht, smul_eq_mul]
    rw [hsum, hpow, show -s - 1 = -(s + 1) by ring, ofReal_sub]
    ring
  have hmellin : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) • psiErrorIndicator t =
      psiErrorIntegral s := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one) fun t ht => ?_).symm
    have : t ∉ Ioi (1 : ℝ) := ht.2
    simp [psiErrorIndicator, indicator_of_notMem this]
  rw [hcongr, integral_add hint1 hint2, hmellin,
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one]
  simp only [ofReal_one, one_cpow]
  congr 1
  have h1 : s - 1 ≠ 0 := fun h0 => by
    have := congrArg re h0
    simp at this
    linarith
  have h2 : -s + 1 ≠ 0 := fun h0 => h1 (by linear_combination -h0)
  field_simp
  ring

/-- The punctured half-plane `{s | 1 / 2 < re s} \ {1}` is preconnected. -/
lemma isPreconnected_halfPlane_inter_compl_one :
    IsPreconnected ({s : ℂ | 1 / 2 < s.re} ∩ {1}ᶜ) := by
  have hA : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hB : IsPreconnected ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC : IsPreconnected ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0}) :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1}) :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hAB := IsPreconnected.union' (s := {s : ℂ | 1 < s.re})
    (t := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}) ⟨2 + I, by simp, by norm_num, by simp⟩ hA hB
  have hABC := IsPreconnected.union' (t := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0})
    ⟨2 - I, Or.inl (by simp), by norm_num, by simp⟩ hAB hC
  have hABCD := IsPreconnected.union' (t := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1})
    ⟨3 / 4 + I, Or.inl (Or.inr ⟨by norm_num, by simp⟩), by norm_num, by norm_num⟩ hABC hD
  convert hABCD using 1
  ext s
  simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff, mem_union]
  constructor
  · rintro ⟨hre, hne⟩
    rcases lt_trichotomy s.re 1 with h1 | h1 | h1
    · exact Or.inr ⟨hre, h1⟩
    · rcases lt_trichotomy s.im 0 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨hre, h2⟩)
      · exact absurd (Complex.ext (by simpa using h1) (by simpa using h2)) hne
      · exact Or.inl (Or.inl (Or.inr ⟨hre, h2⟩))
    · exact Or.inl (Or.inl (Or.inl h1))
  · rintro (((h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨by linarith, fun h0 => by simp [h0] at h1⟩
    · exact ⟨h1, fun h0 => by simp [h0] at h2⟩
    · exact ⟨h1, fun h0 => by simp [h0] at h2⟩
    · exact ⟨h1, fun h0 => by simp [h0] at h2⟩

section Hypothesis

variable (h : ∀ ε : ℝ, 0 < ε →
  (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε))

include h

lemma differentiableAt_mul_psiErrorIntegral {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z : ℂ => z * (1 / (z - 1) + psiErrorIntegral z)) s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_fun_id.sub_const 1
  have h2 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    (differentiableAt_const (1 : ℂ)).fun_div h1 (sub_ne_zero.2 hs1)
  exact differentiableAt_fun_id.fun_mul (h2.fun_add (differentiableAt_psiErrorIntegral h hs))

/-- Under the hypothesis, the identity `ζ'(s) = -ζ(s) * (s * (1 / (s - 1) + H(s)))`, where
`H = psiErrorIntegral`, holds on the whole punctured half-plane `1 / 2 < re s`, `s ≠ 1`. -/
lemma deriv_riemannZeta_add_riemannZeta_mul_eq_zero {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    deriv riemannZeta s + riemannZeta s * (s * (1 / (s - 1) + psiErrorIntegral s)) = 0 := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {1}ᶜ with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  let G : ℂ → ℂ := fun z =>
    deriv riemannZeta z + riemannZeta z * (z * (1 / (z - 1) + psiErrorIntegral z))
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    have h1 : DifferentiableAt ℂ (deriv riemannZeta) z :=
      (analyticOn_riemannZeta z hz.2).deriv.differentiableAt
    have h2 : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz.2
    exact (h1.add (h2.mul
      (differentiableAt_mul_psiErrorIntegral h hz.1 hz.2))).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hUo
  have hzero : G =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz'
    have e1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz'
    rw [LSeries_vonMangoldt_eq_mul_psiErrorIntegral hz'
      (mellinConvergent_psiErrorIndicator h (by linarith)), eq_div_iff hζ] at e1
    simp only [G, Pi.zero_apply]
    linear_combination e1
  exact hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_halfPlane_inter_compl_one
    (show (2 : ℂ) ∈ U from ⟨by norm_num, by simp⟩) hzero ⟨hs, hs1⟩

/-- If `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`, then the Riemann zeta function has no
zeros in the half-plane `1 / 2 < re s`. -/
theorem riemannZeta_ne_zero_of_chebyshev_psi_sub_isBigO {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hUo : IsOpen ({s : ℂ | 1 / 2 < s.re} ∩ {1}ᶜ) :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hK : AnalyticAt ℂ (fun z : ℂ => -(z * (1 / (z - 1) + psiErrorIntegral z))) s := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => -(z * (1 / (z - 1) + psiErrorIntegral z)))
        ({s : ℂ | 1 / 2 < s.re} ∩ {1}ᶜ) := fun z hz =>
      (differentiableAt_mul_psiErrorIntegral h hz.1 hz.2).neg.differentiableWithinAt
    exact hd.analyticOnNhd hUo s ⟨hs, hs1⟩
  have hev : deriv riemannZeta =ᶠ[𝓝 s]
      riemannZeta * fun z : ℂ => -(z * (1 / (z - 1) + psiErrorIntegral z)) := by
    filter_upwards [hUo.mem_nhds ⟨hs, hs1⟩] with z hz
    have := deriv_riemannZeta_add_riemannZeta_mul_eq_zero h hz.1 hz.2
    simp only [Pi.mul_apply]
    linear_combination this
  have h1 := AnalyticAt.analyticOrderAt_deriv_add_one hζ
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hζ hK, hz] at h1
  simp only [sub_zero] at h1
  have htop : analyticOrderAt riemannZeta s = ⊤ := by
    by_contra hne
    generalize analyticOrderAt riemannZeta s = a at h1 hne
    generalize analyticOrderAt (fun z : ℂ => -(z * (1 / (z - 1) + psiErrorIntegral z))) s = k
      at h1
    lift a to ℕ using hne
    cases k with
    | top => simp at h1
    | coe k =>
      norm_cast at h1
      omega
  rw [analyticOrderAt_eq_top] at htop
  have hall := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (show s ∈ ({1}ᶜ : Set ℂ) from hs1) htop (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp)
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by simp) hall

end Hypothesis

end RHPrimeError

/-- If the Riemann zeta function has no zeros in the open half-plane `1 / 2 < re s`, then the
Riemann Hypothesis holds: by the functional equation, the only zeros with `re s < 1 / 2` are the
trivial ones. -/
theorem riemannHypothesis_of_forall_riemannZeta_ne_zero
    (h : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hzero htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  swap
  · exact h s hgt hs1 hzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  have hw : 1 / 2 < (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have hw1 : 1 - s ≠ 1 := fun h0 => hs0 (by linear_combination -h0)
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h0
    have := congrArg re h0
    rw [neg_re, natCast_re] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hzero] at hfe
  have hζ : riemannZeta (1 - s) ≠ 0 := h _ hw hw1
  have hΓ : Gamma (1 - s) ≠ 0 := Gamma_ne_zero hwn
  have hpow : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h0 => mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) h0.1
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζ hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have h3 : (π : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    have h4 := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination h4
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases eq_or_lt_of_le hk0 with hk0 | hk0
    · exact hs0 (by simp [hsk, hk0])
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have : s.re = -2 * (k : ℝ) := by simp [hsk]
      linarith
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hcast
  rw [hcast, hsk]
  push_cast
  ring

/-- **A square-root error term for the Chebyshev function implies the Riemann Hypothesis**:
if `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`, then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_chebyshev_psi_sub_isBigO
    (h : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_forall_riemannZeta_ne_zero fun _ hs hs1 =>
    RHPrimeError.riemannZeta_ne_zero_of_chebyshev_psi_sub_isBigO h hs hs1
