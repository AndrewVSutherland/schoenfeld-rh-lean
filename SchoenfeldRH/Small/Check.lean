import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The finite range: a kernel-friendly checker for `|ψ(x) - x| < √x log² x / (8π)`

Everything here is elementary and depends on Mathlib only.

## Idea

`ψ(n) = log L_n` with `L_n = lcm(1, …, n)` (`Chebyshev.psi_eq_log_lcmUpto`), and `L_n` is computed exactly
in `ℕ` by `L_n = lcm(L_{n-1}, n)`.  For integers `a ≤ b` and real `x ∈ [a, b + 1)` we have
`ψ(a) ≤ ψ(x) ≤ ψ(b)`, hence `|ψ(x) - x| < f(x)` (with `f(x) = √x log² x / (8π)`, increasing) follows from

* `ψ(b) - a < f(a)`, and
* `b + 1 - ψ(a) < f(a)`.

These are verified through natural numbers `s, kp, ka, kb` (certificate data) with

* `s² ≤ a·2²⁰` (so `s/2¹⁰ ≤ √a`), `2^kp ≤ a⁶⁴` (so `kp·log 2/64 ≤ log a`),
* `2^ka ≤ L_a` (so `ka·log 2 ≤ ψ(a)`), `L_b < 2^kb` (so `ψ(b) < kb·log 2`),

Mathlib's `0.6931471803 < log 2 < 0.6931471808` and `π < 3.1416`, and two inequalities between natural
numbers (`checkIv`).

## Kernel evaluation

The certificate is one closed term `walk dataEnd data 73 (lcmRun 73 73 1) = true`, evaluated by the kernel
(`decide +kernel`).  The definitions are written for *every* kernel, not only for Lean's:

* only `Nat.add/sub/mul/div/mod/gcd/pow/ble/beq` on literals are used (no `Nat.log2`, which is not
  accelerated; bit lengths are certificate data);
* every accumulator is forced to a literal before the next step (`forceNat`, `forceB`: a `Nat.rec` on the
  value), so evaluation does not rely on a kernel's caching of shared thunks, and each loop iteration
  passes through one δ-step (`forceNat`), which keeps the recursion depth of Lean's `whnf` bounded;
* the remainders `L mod n` of the large number `L` are obtained in batches of `batchSize = 32`
  consecutive `n`: one division `R = L mod (n₁ ⋯ n₃₂)`, then small numbers only (`incStep`).  A checker
  with a slow (bit-serial) bignum division pays one large division per batch instead of one per `n`.
-/

namespace SchoenfeldRH.Small

open Chebyshev
open Nat (lcmUpto)

/-! ### Forcing -/

/-- `forceNat n k = k n`; a kernel has to evaluate `n` to a literal first. -/
noncomputable def forceNat (n : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.rec (k 0) (fun n' _ => k (Nat.succ n')) n

theorem forceNat_eq (n : ℕ) (k : ℕ → ℕ) : forceNat n k = k n := by
  cases n <;> rfl

/-- `forceB n k = k n`; a kernel has to evaluate `n` to a literal first. -/
noncomputable def forceB (n : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (k 0) (fun n' _ => k (Nat.succ n')) n

theorem forceB_eq (n : ℕ) (k : ℕ → Bool) : forceB n k = k n := by
  cases n <;> rfl

/-! ### The lcm walk -/

/-- One step inside a batch.  If `R ≡ L [MOD n]` then `L * incStep R I n = lcm (L * I) n`. -/
def incStep (R I n : ℕ) : ℕ :=
  Nat.mul I (Nat.div n (Nat.gcd n (Nat.mod (Nat.mul R I) n)))

/-- `incRun R N c I`: apply `incStep R · n` for `n = N - c + 1, …, N` to `I`. -/
noncomputable def incRun (R N c : ℕ) : ℕ → ℕ :=
  Nat.rec (fun I => I) (fun c ih I => forceNat (incStep R I (Nat.sub N c)) ih) c

/-- `prodRun N c P = P * ∏ n ∈ (N - c, N], n`. -/
noncomputable def prodRun (N c : ℕ) : ℕ → ℕ :=
  Nat.rec (fun P => P) (fun c ih P => forceNat (Nat.mul P (Nat.sub N c)) ih) c

/-- One batch: from `L = lcm(1..N-c)` to `lcm(1..N)`. -/
noncomputable def lcmBatch (L N c : ℕ) : ℕ :=
  forceNat (prodRun N c 1) fun P => forceNat (Nat.mod L P) fun R => Nat.mul L (incRun R N c 1)

/-- `q` batches of length `k`, the last one ending at `N`. -/
noncomputable def lcmRunB (k N q : ℕ) : ℕ → ℕ :=
  Nat.rec (fun L => L) (fun q ih L => forceNat (lcmBatch L (Nat.sub N (Nat.mul q k)) k) ih) q

/-- Length of the full batches of `lcmRun`. -/
def batchSize : ℕ := 32

/-- `lcmRun b cnt L`: from `L = lcm(1..b-cnt)` to `lcm(1..b)`: one batch of length `cnt % 32`, then
`cnt / 32` batches of length `32`. -/
noncomputable def lcmRun (b cnt L : ℕ) : ℕ :=
  forceNat (lcmBatch L (Nat.sub b (Nat.mul (Nat.div cnt batchSize) batchSize)) (Nat.mod cnt batchSize))
    (lcmRunB batchSize b (Nat.div cnt batchSize))

theorem incStep_eq (R I n : ℕ) : incStep R I n = I * (n / Nat.gcd n (R * I % n)) := rfl

theorem incRun_zero (R N I : ℕ) : incRun R N 0 I = I := rfl

theorem incRun_succ (R N c I : ℕ) : incRun R N (c + 1) I = incRun R N c (incStep R I (N - c)) :=
  forceNat_eq (incStep R I (N - c)) (incRun R N c)

theorem prodRun_zero (N P : ℕ) : prodRun N 0 P = P := rfl

theorem prodRun_succ (N c P : ℕ) : prodRun N (c + 1) P = prodRun N c (P * (N - c)) :=
  forceNat_eq (P * (N - c)) (prodRun N c)

theorem lcmBatch_eq (L N c : ℕ) : lcmBatch L N c = L * incRun (L % prodRun N c 1) N c 1 := by
  simp only [lcmBatch, forceNat_eq]; rfl

theorem lcmRunB_zero (k N L : ℕ) : lcmRunB k N 0 L = L := rfl

theorem lcmRunB_succ (k N q L : ℕ) :
    lcmRunB k N (q + 1) L = lcmRunB k N q (lcmBatch L (N - q * k) k) :=
  forceNat_eq (lcmBatch L (N - q * k) k) (lcmRunB k N q)

theorem lcmRun_eq (b cnt L : ℕ) :
    lcmRun b cnt L = lcmRunB 32 b (cnt / 32) (lcmBatch L (b - cnt / 32 * 32) (cnt % 32)) := by
  simp only [lcmRun, forceNat_eq]; rfl

theorem lcmUpto_zero : lcmUpto 0 = 1 := by simp [lcmUpto]

theorem lcmUpto_succ (n : ℕ) : lcmUpto (n + 1) = Nat.lcm (lcmUpto n) (n + 1) := by
  rw [lcmUpto, lcmUpto, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert,
    id, lcm_eq_nat_lcm, Nat.lcm_comm]

/-- The basic step: with `R = L % P` and `n ∣ P`, the batch increment `I` is updated correctly. -/
theorem mul_incStep {L P R I n : ℕ} (hR : R = L % P) (hn : n ∣ P) :
    L * incStep R I n = Nat.lcm (L * I) n := by
  have h1 : R * I ≡ L * I [MOD n] := by
    rw [hR]; exact ((Nat.mod_modEq L P).of_dvd hn).mul_right I
  have h2 : Nat.gcd n (R * I % n) = Nat.gcd (L * I) n := by
    rw [Nat.gcd_comm n, ← Nat.gcd_rec, Nat.gcd_comm n, h1.gcd_eq]
  rw [incStep_eq, h2, ← mul_assoc, Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

theorem prodRun_dvd (N : ℕ) : ∀ c P : ℕ, P ∣ prodRun N c P ∧ ∀ j < c, (N - j) ∣ prodRun N c P := by
  intro c
  induction c with
  | zero => intro P; exact ⟨dvd_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ c ih =>
    intro P
    rw [prodRun_succ]
    obtain ⟨h1, h2⟩ := ih (P * (N - c))
    refine ⟨(Dvd.intro _ rfl).trans h1, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h2 j hj
    · exact (Dvd.intro_left _ rfl).trans h1

theorem mul_incRun {L P R N : ℕ} (hR : R = L % P) :
    ∀ c I : ℕ, c ≤ N → (∀ j < c, (N - j) ∣ P) → L * I = lcmUpto (N - c) →
      L * incRun R N c I = lcmUpto N := by
  intro c
  induction c with
  | zero => intro I _ _ h; simpa [incRun_zero] using h
  | succ c ih =>
    intro I hc hP h
    rw [incRun_succ]
    refine ih _ (by omega) (fun j hj => hP j (by omega)) ?_
    rw [mul_incStep hR (hP c (by omega)), h]
    have : N - c = (N - (c + 1)) + 1 := by omega
    rw [this, lcmUpto_succ]

theorem lcmBatch_lcmUpto {N c : ℕ} (hc : c ≤ N) : lcmBatch (lcmUpto (N - c)) N c = lcmUpto N := by
  rw [lcmBatch_eq]
  exact mul_incRun rfl c 1 hc (prodRun_dvd N c 1).2 (mul_one _)

theorem lcmRunB_lcmUpto (k N : ℕ) :
    ∀ q : ℕ, q * k ≤ N → lcmRunB k N q (lcmUpto (N - q * k)) = lcmUpto N := by
  intro q
  induction q with
  | zero => intro _; simp [lcmRunB_zero]
  | succ q ih =>
    intro hq
    have hq' : (q + 1) * k = q * k + k := Nat.succ_mul q k
    rw [lcmRunB_succ]
    have h1 : N - (q + 1) * k = (N - q * k) - k := by omega
    rw [h1, lcmBatch_lcmUpto (by omega)]
    exact ih (by omega)

theorem lcmRun_lcmUpto {b cnt : ℕ} (h : cnt ≤ b) : lcmRun b cnt (lcmUpto (b - cnt)) = lcmUpto b := by
  have hdm : cnt / 32 * 32 + cnt % 32 = cnt := Nat.div_add_mod' cnt 32
  rw [lcmRun_eq]
  have h1 : b - cnt = (b - cnt / 32 * 32) - cnt % 32 := by omega
  rw [h1, lcmBatch_lcmUpto (by omega)]
  exact lcmRunB_lcmUpto 32 b (cnt / 32) (by omega)

/-! ### The check for one interval -/

/-- The inequalities for an interval `[a, b]`; `La`, `Lb` are `lcm(1..a)`, `lcm(1..b)`. -/
def checkIv (a b s kp ka kb La Lb : ℕ) : Bool :=
  Nat.ble a b && Nat.ble (s * s) (a * 2 ^ 20) && Nat.ble (2 ^ kp) (a ^ 64) &&
  Nat.ble (2 ^ ka) La && Nat.blt Lb (2 ^ kb) &&
  Nat.blt (kb * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))
    (s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
      + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)) &&
  Nat.blt ((b + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))
    (s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
      + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))

theorem checkIv_iff {a b s kp ka kb La Lb : ℕ} :
    checkIv a b s kp ka kb La Lb = true ↔
      a ≤ b ∧ s * s ≤ a * 2 ^ 20 ∧ 2 ^ kp ≤ a ^ 64 ∧ 2 ^ ka ≤ La ∧ Lb < 2 ^ kb ∧
      kb * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) ∧
      (b + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by
  simp only [checkIv, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, and_assoc]

/-- Soundness of `checkIv`: the bound on `[a, b + 1)`. -/
theorem bound_of_checkIv {a b s kp ka kb : ℕ}
    (h : checkIv a b s kp ka kb (lcmUpto a) (lcmUpto b) = true) {x : ℝ}
    (hx1 : (a : ℝ) ≤ x) (hx2 : x < (b : ℝ) + 1) :
    |ψ x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  obtain ⟨-, hs, hkp, hka, hkb, hU, hL⟩ := checkIv_iff.mp h
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp at hkp
    · exact h
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
  have hx0 : 0 < x := by linarith
  -- `ψ` on the interval
  have hψa : (ka : ℝ) * Real.log 2 ≤ ψ x := by
    calc (ka : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ ka) := by rw [Real.log_pow]
      _ ≤ Real.log (lcmUpto a) := Real.log_le_log (by positivity) (by exact_mod_cast hka)
      _ = ψ a := (psi_eq_log_lcmUpto a).symm
      _ ≤ ψ x := psi_mono hx1
  have hψb : ψ x < (kb : ℝ) * Real.log 2 := by
    have hfl : ⌊x⌋₊ ≤ b := by
      have : ⌊x⌋₊ < b + 1 := (Nat.floor_lt hx0.le).mpr (by exact_mod_cast hx2)
      omega
    calc ψ x = ψ ⌊x⌋₊ := psi_eq_psi_coe_floor x
      _ ≤ ψ b := psi_mono (by exact_mod_cast hfl)
      _ = Real.log (lcmUpto b) := psi_eq_log_lcmUpto b
      _ < Real.log ((2 : ℝ) ^ kb) :=
          Real.log_lt_log (by exact_mod_cast Nat.lcmUpto_pos b) (by exact_mod_cast hkb)
      _ = kb * Real.log 2 := Real.log_pow _ _
  -- `log a` and `√a`
  have hloga : (kp : ℝ) * Real.log 2 ≤ 64 * Real.log a := by
    calc (kp : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ kp) := by rw [Real.log_pow]
      _ ≤ Real.log ((a : ℝ) ^ 64) := Real.log_le_log (by positivity) (by exact_mod_cast hkp)
      _ = 64 * Real.log a := by rw [Real.log_pow]; norm_num
  have hsq : (s : ℝ) / 2 ^ 10 ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    have hs' : (s : ℝ) * s ≤ a * 2 ^ 20 := by exact_mod_cast hs
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d4
  -- the rational lower bound `F ≤ f(a) ≤ f(x)`
  have hF : (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416)
      ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    have h1 : (kp : ℝ) * 0.6931471803 / 64 ≤ Real.log a := by
      have : (kp : ℝ) * 0.6931471803 ≤ kp * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
      linarith
    have h2 : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx1
    have h3 : Real.sqrt a ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
    have h0 : (0 : ℝ) ≤ (kp : ℝ) * 0.6931471803 / 64 := by positivity
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    calc (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416)
        ≤ Real.sqrt x * Real.log x ^ 2 / (8 * 3.1416) := by
          gcongr
          · exact hsq.trans h3
          · exact h1.trans h2
      _ ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
          gcongr
  -- the two integer inequalities, over `ℝ`
  have hUr : (kb : ℝ) * 0.6931471808 - a
      < (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416) := by
    have hU' : (kb : ℝ) * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by exact_mod_cast hU
    norm_num at hU' ⊢
    linarith
  have hLr : (b : ℝ) + 1 - ka * 0.6931471803
      < (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416) := by
    have hL' : ((b : ℝ) + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by exact_mod_cast hL
    norm_num at hL' ⊢
    linarith
  have hka' : (ka : ℝ) * 0.6931471803 ≤ ka * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
  have hkb' : (kb : ℝ) * Real.log 2 ≤ kb * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2'.le (Nat.cast_nonneg _)
  rw [abs_lt]
  constructor <;> linarith

/-! ### The walk over all intervals -/

/-- `walk final data a La`: starting at `a` with `La = lcm(1..a)`, check the consecutive intervals
`[a, b]` listed in `data` (entries `(b, s, kp, ka, kb)`; the next interval starts at `b + 1`), and
finally that the next start equals `final`. -/
noncomputable def walk (final : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | [], a, _ => Nat.beq a final
  | (b, s, kp, ka, kb) :: rest, a, La =>
    forceB (lcmRun b (b - a) La) fun Lb =>
      checkIv a b s kp ka kb La Lb &&
        forceB (lcmBatch Lb (b + 1) 1) fun L' => walk final rest (b + 1) L'

/-- Soundness of `walk`. -/
theorem bound_of_walk (final : ℕ) :
    ∀ (data : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (a : ℕ), walk final data a (lcmUpto a) = true →
      ∀ x : ℝ, (a : ℝ) ≤ x → x < (final : ℝ) →
        |ψ x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  intro data
  induction data with
  | nil =>
    intro a h x hx1 hx2
    have : a = final := Nat.eq_of_beq_eq_true (by simpa [walk] using h)
    subst this
    exact absurd hx2 (not_lt.mpr hx1)
  | cons e rest ih =>
    obtain ⟨b, s, kp, ka, kb⟩ := e
    intro a h x hx1 hx2
    simp only [walk, forceB_eq, Bool.and_eq_true] at h
    obtain ⟨hc, hw⟩ := h
    have hab : a ≤ b := (checkIv_iff.mp hc).1
    have h1 : lcmRun b (b - a) (lcmUpto a) = lcmUpto b := by
      have := lcmRun_lcmUpto (b := b) (cnt := b - a) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hab] at this
    have h2 : lcmBatch (lcmUpto b) (b + 1) 1 = lcmUpto (b + 1) := by
      have := lcmBatch_lcmUpto (N := b + 1) (c := 1) (by omega)
      rwa [Nat.add_sub_cancel] at this
    rw [h1] at hc hw
    rw [h2] at hw
    rcases lt_or_ge x ((b : ℝ) + 1) with hx | hx
    · exact bound_of_checkIv hc hx1 hx
    · exact ih (b + 1) hw x (by exact_mod_cast hx) hx2

end SchoenfeldRH.Small
