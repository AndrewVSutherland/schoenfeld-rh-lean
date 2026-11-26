import Mathlib

/-!
# Integrability of a series of integrable functions with summable `L¹` norms
-/

open MeasureTheory

namespace SchoenfeldRH.Lemmas.p8

theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF : ∀ i, Integrable (F i)) (hs : Summable fun i => ∫ t, ‖F i t‖) :
    Integrable (fun t => ∑' i, F i t) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hF i).1), ?_⟩
  have h1 : ∀ i, ∫⁻ a, ‖F i a‖ₑ = ENNReal.ofReal (∫ a, ‖F i a‖) := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    simp only [ofReal_norm]
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ := lintegral_tsum (fun i => (hF i).1.enorm)
    _ = ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖) := tsum_congr h1
    _ = ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end SchoenfeldRH.Lemmas.p8
-- stamp: 1
