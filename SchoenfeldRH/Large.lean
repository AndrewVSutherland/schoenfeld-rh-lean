import Mathlib

/-!
# Contract F: the final inequality for `x ≥ 30000`

Blueprint v2, section 4. From the explicit-formula bounds (U), (L) (Contract E) and the zero-sum
bound (Contract Z), taken as hypotheses on an abstract function `W`, we derive
`|ψ(x) - x| < √x log² x / (8π)` for all real `x ≥ 30000`.

Only elementary numerics are used: `e` to nine decimals (`Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`)
and `π` to four decimals (`Real.pi_gt_d4`, `Real.pi_lt_d4`).
-/

namespace SchoenfeldRH

namespace Large

open Real

/-- `log π ≥ 1.134`, from `log (π / e) ≥ 1 - e / π`. -/
lemma log_pi_gt : (1.134 : ℝ) ≤ Real.log π := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hp := Real.pi_gt_d4
  have hpe : 0 < π / Real.exp 1 := by positivity
  have h1 := Real.one_sub_inv_le_log_of_pos hpe
  rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp, inv_div] at h1
  have h2 : Real.exp 1 / π ≤ 0.866 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  linarith

/-- `exp 4 < 55`. -/
lemma exp_four_lt : Real.exp 4 < 55 := by
  have he := Real.exp_one_lt_d9
  have h0 := (Real.exp_pos 1).le
  have : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 55 := by norm_num

/-- For `t > 0`: `log t ≤ 2 √t / e`. -/
lemma log_le_two_sqrt_div_e {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t / Real.exp 1 := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have he := Real.exp_pos 1
  have h1 := Real.log_le_sub_one_of_pos (div_pos hs he)
  rw [Real.log_div hs.ne' he.ne', Real.log_exp, Real.log_sqrt ht.le] at h1
  have : Real.log t ≤ 2 * (Real.sqrt t / Real.exp 1) := by linarith
  calc Real.log t ≤ 2 * (Real.sqrt t / Real.exp 1) := this
    _ = 2 * Real.sqrt t / Real.exp 1 := by ring

/-- The key real inequality: for `y ≥ 173.2`,
`y + (y + 1) (log²(y/π)/(2π) + 1/2) + 4 < y log² y / (2π)`. -/
lemma key {y : ℝ} (hy : 173.2 ≤ y) :
    y + (y + 1) * (Real.log (y / π) ^ 2 / (2 * π) + 1 / 2) + 4
      < y * Real.log y ^ 2 / (2 * π) := by
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hy0 : 0 < y := by linarith
  set t := y / π with ht_def
  have ht0 : 0 < t := by positivity
  have hyt : y = π * t := by rw [ht_def]; field_simp
  -- `log y = L + p`
  set L := Real.log t with hL_def
  set p := Real.log π with hp_def
  have hlogy : Real.log y = L + p := by
    rw [hyt, Real.log_mul hpi0.ne' ht0.ne', add_comm]
  have hp := log_pi_gt
  -- `L ≥ 4`
  have ht55 : 55 ≤ t := by
    rw [ht_def, le_div_iff₀ hpi0]; nlinarith
  have hL4 : 4 ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le ht0]; linarith [exp_four_lt]
  -- `L² ≤ 4 t / e²`
  have hLs := log_le_two_sqrt_div_e ht0
  have he := Real.exp_one_gt_d9
  have he0 := Real.exp_pos 1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hLsq : L ^ 2 * Real.exp 1 ^ 2 ≤ 4 * t := by
    have h1 : L * Real.exp 1 ≤ 2 * Real.sqrt t := by
      rw [le_div_iff₀ he0] at hLs; exact hLs
    have h2 : 0 ≤ L * Real.exp 1 := by positivity
    nlinarith
  have hL2 : L ^ 2 ≤ 0.55 * t := by
    have : (7.38 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith
    nlinarith
  -- reduce to a polynomial inequality
  rw [hlogy, ← sub_pos]
  have h2pi : 0 < 2 * π := by positivity
  have hexpr : y * (L + p) ^ 2 / (2 * π) -
      (y + (y + 1) * (L ^ 2 / (2 * π) + 1 / 2) + 4)
      = (y * p * (2 * L + p) - 3 * π * y - L ^ 2 - 9 * π) / (2 * π) := by
    field_simp; ring
  rw [hexpr]
  apply div_pos _ h2pi
  have hpp : 10.35 ≤ p * (2 * L + p) := by nlinarith
  have : 10.35 * y ≤ y * p * (2 * L + p) := by nlinarith
  -- `L² ≤ 0.55 t = 0.55 y / π ≤ 0.18 y`
  have hL2y : L ^ 2 ≤ 0.18 * y := by
    have : 0.55 * t ≤ 0.18 * y := by
      rw [ht_def, mul_div_assoc', div_le_iff₀ hpi0]; nlinarith
    linarith
  nlinarith

/-- `√n` is never of the form `2k + 1/2`. -/
lemma sqrt_ne (n k : ℕ) : Real.sqrt n - 1 / 2 ≠ 2 * k := by
  intro h
  have hs : Real.sqrt n = 2 * k + 1 / 2 := by linarith
  have h2 : ((n : ℕ) : ℝ) = (2 * k + 1 / 2) ^ 2 := by
    rw [← hs, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h3 : ((4 * n : ℕ) : ℝ) = ((4 * (4 * k ^ 2 + 2 * k) + 1 : ℕ) : ℝ) := by
    push_cast; rw [h2]; ring
  have h4 : 4 * n = 4 * (4 * k ^ 2 + 2 * k) + 1 := by exact_mod_cast h3
  omega

/-- The bound at natural `n ≥ 30000`, in the form
`ψ(n) - n ≤ y + (y+1) Z + 4` and `n - ψ(n) ≤ y + (y+1) Z + 3`, where `y = √n`
and `Z = log²(y/π)/(2π) + 1/2`. -/
lemma nat_bound (W : ℝ → ℝ)
    (hU : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam →
      Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * W (lam - 1 / 2)) + 3)
    (hL : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam → (∀ k : ℕ, lam ≠ 2 * k) →
      x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * W (lam + 1 / 2)) + 3)
    (hZ : ∀ B : ℝ, 50 ≤ B → B * W B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2)
    (hW : ∀ B : ℝ, 0 ≤ W B) (n : ℕ) (hn : 30000 ≤ n) :
    let y := Real.sqrt n
    let Z := Real.log (y / π) ^ 2 / (2 * π) + 1 / 2
    173.2 ≤ y ∧ Chebyshev.psi n - n ≤ y + (y + 1) * Z + 4 ∧
      (n : ℝ) - Chebyshev.psi n ≤ y + (y + 1) * Z + 3 := by
  intro y Z
  have hn' : (30000 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 173.2 ≤ y := Real.le_sqrt_of_sq_le (by linarith)
  have hy0 : 0 < y := by linarith
  have hyy : y ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hZ0 : 0 ≤ Z := by positivity
  have hWy := hW y
  have hZy : y * W y ≤ Z := hZ y (by linarith)
  have h2 : 2 ≤ n := by omega
  have hUy := hU n (y + 1 / 2) h2 (by linarith)
  have hLy := hL n (y - 1 / 2) h2 (by linarith) (sqrt_ne n)
  have hsy : Real.sqrt (n : ℝ) = y := rfl
  rw [hsy] at hUy hLy
  clear_value Z y
  refine ⟨hy, ?_, ?_⟩
  · have h := hUy
    rw [show y + 1 / 2 - 1 / 2 = y by ring] at h
    have hd : (n : ℝ) / (y + 1 / 2 - 1) ≤ y + 1 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : y * ((y + 1 / 2) * W y) ≤ (y + 1) * Z := by
      have : y * ((y + 1 / 2) * W y) = (y + 1 / 2) * (y * W y) := by ring
      rw [this]
      calc (y + 1 / 2) * (y * W y) ≤ (y + 1 / 2) * Z := by gcongr
        _ ≤ (y + 1) * Z := by gcongr; linarith
    linarith
  · have h := hLy
    rw [show y - 1 / 2 + 1 / 2 = y by ring] at h
    have hd : (n : ℝ) / (y - 1 / 2 + 1) ≤ y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : (y + 1) * ((y - 1 / 2) * W y) ≤ (y + 1) * Z := by
      gcongr
      nlinarith
    linarith

end Large

open Large in
theorem schoenfeld_large_of_contracts (W : ℝ → ℝ)
    (hU : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam →
      Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * W (lam - 1 / 2)) + 3)
    (hL : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam → (∀ k : ℕ, lam ≠ 2 * k) →
      x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * W (lam + 1 / 2)) + 3)
    (hZ : ∀ B : ℝ, 50 ≤ B → B * W B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2)
    (hW : ∀ B : ℝ, 0 ≤ W B) :
    ∀ x : ℝ, 30000 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  intro x hx
  set n := ⌊x⌋₊ with hn_def
  have hx0 : 0 ≤ x := by linarith
  have hn : 30000 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  obtain ⟨hy, hup, hlo⟩ := nat_bound W hU hL hZ hW n hn
  set y := Real.sqrt n with hy_def
  have hk := key hy
  have hpsi : Chebyshev.psi x = Chebyshev.psi n := Chebyshev.psi_eq_psi_coe_floor x
  -- `f(n) = y log² y / (2π)` and `f(n) ≤ f(x)`
  have hn0 : (0 : ℝ) < n := by
    have : (30000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfn : Real.sqrt n * Real.log n ^ 2 / (8 * Real.pi) = y * Real.log y ^ 2 / (2 * Real.pi) := by
    have : Real.log n = 2 * Real.log y := by
      rw [hy_def, Real.log_sqrt hn0.le]; ring
    rw [this]; field_simp; ring
  have hfmono : Real.sqrt n * Real.log n ^ 2 / (8 * Real.pi) ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hl : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
    gcongr
  rw [hpsi, abs_lt]
  constructor <;> linarith

end SchoenfeldRH
