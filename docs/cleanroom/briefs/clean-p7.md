## Your assignment: NAME = p7
Owned files: SchoenfeldRH/Explicit/Weighted.lean (3 statements; the definition `Kmu` must not be changed) and
SchoenfeldRH/Explicit/LogDeriv.lean (5 statements; the definition `trivZero` must not be changed), helper dir
SchoenfeldRH/Lemmas/p7/.
You may use, as black boxes, the statements (stubs of other provers) in SchoenfeldRH/Explicit/Kernel.lean,
SchoenfeldRH/Base/*.lean and SchoenfeldRH/ZeroSum/Basic.lean.
Mathematical notes from the lead (use or ignore):
- Weighted.lean. `Kmu c μ y t = y^s (1/s - 1/(s + μ))` with `s = c + t i`; `integrable_Kmu` and `integral_Kmu` are
  restatements of the stubs `integrable_kappa`/`perron_kernel` in Kernel.lean (norm of `y^s` is `y^c`).
  `perron_weighted_mu`: for an absolutely convergent Dirichlet series `L(s) = Σ a(n) n^(-s)` on `Re s = c`,
  `Σ_{0<n<N} a(n)(1 - (n/N)^μ) = (1/2π) ∫ L(s) N^s (1/s - 1/(s + μ)) dt`: integrate termwise (dominated convergence /
  `integral_tsum`-type lemma with the summable majorant `‖a n‖ n^(-c) ∫‖Kmu‖`), each term being Perron's formula with
  `y = N/n` (`n = N` and `n > N` contribute `0`, and `n = 0` contributes nothing to an `LSeries`).
- LogDeriv.lean. `trivZero k = -2 (k + 1)`. `hasSum_trivZero` is the digamma series (stub `hasSum_digamma` in
  Base/Digamma.lean, at `w = s/2 + 1`, with `ψ(1) = -γ` and the recurrence `ψ(z + 1) = ψ(z) + 1/z`).
  `neg_logDeriv_zeta_eq`: combine the stub `logDeriv_riemannZeta_eq` (Base/Xi.lean), the Hadamard sum
  `hasSum_hadamard_xiZeta` (ZeroSum/Basic.lean), the value `ξ'/ξ(0) = (1/2) log (4π) - 1 - γ/2` (from the stubs
  `deriv_xiZeta_zero`, `xiZeta_zero` and Mathlib's value of `completedRiemannZeta₀` at 0 or 1), and `hasSum_trivZero`;
  the constants combine to `1 - log (2π)`.
