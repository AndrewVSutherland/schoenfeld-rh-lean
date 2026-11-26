## Your assignment: NAME = p1
Owned files: SchoenfeldRH/Base/Xi.lean and SchoenfeldRH/Base/Constants.lean (9 + 2 statements), helper dir SchoenfeldRH/Lemmas/p1/.
`xiZeta` is defined in SchoenfeldRH/Base/XiDef.lean (do not edit): `xiZeta s = s * (s - 1) * completedRiemannZeta₀ s + 1`.
Everything is to be proved from Mathlib alone (no stubs of other provers needed).
Mathematical notes from the lead (use or ignore):
- Mathlib's `completedRiemannZeta₀` is entire and `completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1 - s)`;
  `completedRiemannZeta` is `π^(-s/2) Γ(s/2) ζ(s)` away from `s = 0` (see Mathlib/NumberTheory/LSeries/RiemannZeta.lean and
  HurwitzZetaEven.lean), with the functional equation `Λ(1 - s) = Λ(s)`.
- Zeros of ξ: for `Re s ≥ 1`, `ζ(s) ≠ 0` (Mathlib has nonvanishing on `Re s ≥ 1`) and the Gamma factor does not vanish; for
  `Re s ≤ 0` use the functional equation; `ξ(0) = ξ(1) = 1`.
- Countability: a nonzero entire function has countably many zeros (its zero set is discrete / it is analytic and not
  identically zero).
- `logDeriv_riemannZeta_eq`: logarithmic differentiation of `ξ(s) = s (s - 1) π^(-s/2) Γ(s/2) ζ(s)` for `Re s > 1`.
- Constants: Mathlib knows the value of `completedRiemannZeta₀ 1` in terms of the Euler–Mascheroni constant and `log (4π)`
  (search for `completedRiemannZeta₀_one`); for the numerical inequality you need `γ < 0.5811` or so and a lower bound for
  `log (4π)`: Mathlib has bounds for `Real.eulerMascheroniConstant` through the sequences in
  Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean, and `Real.pi_gt_d2`-style bounds for π. Keep the arithmetic light.
