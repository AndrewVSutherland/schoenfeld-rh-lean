## Your assignment: NAME = p6
Owned file: SchoenfeldRH/Explicit/Kernel.lean (5 statements; the definitions `pairK`, `pairE` must not be changed),
helper dir SchoenfeldRH/Lemmas/p6/. To be proved from Mathlib alone.
Mathematical notes from the lead (use or ignore). Write `s = c + t i`:
- `perron_kernel`: Perron's formula `(1/2πi) ∫_{(c)} y^s (1/s - 1/(s + μ)) ds = (1 - y^(-μ))·[y ≥ 1]` for `c > 0`,
  `c + μ > 1`. The integrand is `O(1/t²)` (since `1/s - 1/(s+μ) = μ/(s(s+μ))`), hence integrable (`integrable_kappa`).
  One route is Mathlib's Mellin inversion theorem (Mathlib/Analysis/MellinInversion.lean, `mellinInv_mellin_eq`) applied
  to an explicit function supported on `(0, 1]` such as `u ↦ 1 - u^μ` (its Mellin transform is `1/s - 1/(s + μ)`), with
  `y = 1/u`; note the value at the jump/corner `y = 1` is `0` on both sides here because the function is continuous.
- `pair_mul_kappa` is algebra: `(1/(s - w) + 1/w)(1/s - 1/(s + μ)) = μ/(w (s - w)(s + μ))`.
- `integral_pairK`: partial fractions `μ/(w (s - w)(s + μ)) = (μ/(w (w + μ)))·(1/(s - w) - 1/(s + μ))` and Perron's
  formula for `1/(s - w)` and `1/(s + μ)` at `x ≥ 1` (again Mellin inversion for `u^(-w)` and `u^μ` on `(0, 1]`); the two
  individual integrals are only conditionally convergent, so work with the difference, which is `O(1/t²)`.
- `integral_norm_pairK_le`: a uniform `L¹` bound. `‖pairK x c μ w t‖ = x^c |μ| / (|w| |s - w| |s + μ|)`; with
  `|s - w| ≥ δ` and `|s + μ| ≥ 1`... one way is Cauchy–Schwarz or splitting the `t`-line, using
  `∫ dt/(|s - w| |s + μ|) ≲ (1 + |μ - 1|)^(1/2) |w|^(-1/2)`-type estimates; only the stated form of the bound matters
  (the constant `K` may depend on `δ` only).
