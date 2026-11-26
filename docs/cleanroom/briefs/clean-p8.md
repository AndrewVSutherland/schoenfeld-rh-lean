## Your assignment: NAME = p8
Owned file: SchoenfeldRH/Explicit/Formula.lean (1 statement: `explicit_formula_mu`), helper dir SchoenfeldRH/Lemmas/p8/.
You may use, as black boxes, the statements (stubs of other provers) in SchoenfeldRH/Explicit/Kernel.lean,
Explicit/Weighted.lean, Explicit/LogDeriv.lean, SchoenfeldRH/ZeroSum/Basic.lean and SchoenfeldRH/Base/*.lean. Read them all
first: they were designed to be the ingredients of this theorem.
Mathematical notes from the lead (use or ignore). Fix a natural `x ≥ 1`, real `μ` with `μ > 0` or `μ < -1`, and a line
`Re s = c` with `c > 1` and `c + μ > 1` (e.g. `c = 2` if `μ > 0`, `c = 2 - μ` if `μ < -1`); write `κ(s) = 1/s - 1/(s + μ)`.
1. `perron_weighted_mu` with `a = Λ` (von Mangoldt; its L-series is `-ζ'/ζ` for `Re s > 1`, Mathlib:
   `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`) gives
   `Σ_{0<n<x} Λ(n)(1 - (n/x)^μ) = (1/2π) ∫ (-ζ'/ζ(s)) x^s κ(s) dt`.
2. On the line, `neg_logDeriv_zeta_eq`: `-ζ'/ζ(s) = (1/(s-1) + 1) - log 2π - Σ_ρ m_ρ (1/(s-ρ) + 1/ρ) - Σ_k (1/(s-τ_k) + 1/τ_k)`
   with `τ_k = trivZero k`. Also `1/(s-1) + 1 = 1/(s - 1) + 1/1`, the same shape with the "pole" `w = 1`.
3. For each `w` with `Re w < c`, `w ≠ 0`, `w + μ ≠ 0`: `(1/(s-w) + 1/w) x^s κ(s) = pairK x c μ w t` (`pair_mul_kappa`) and
   `∫ pairK = 2π pairE x μ w` (`integral_pairK`). The constant term: `(1/2π) ∫ x^s κ(s) dt = 1 - x^(-μ)` (`integral_Kmu`).
4. Interchange `∫` with the two infinite sums: `integral_norm_pairK_le` gives `∫ ‖pairK x c μ w t‖ dt ≤ K' ‖w‖^(-3/2)`
   uniformly, and `Σ_ρ m_ρ ‖ρ‖^(-3/2) < ∞` by the first part of `hadamard_logDeriv` applied to ξ (stubs
   `differentiable_xiZeta`, `xiZeta_zero`, `xiZeta_growth`), `Σ_k ‖τ_k‖^(-3/2) < ∞` directly. A summable family of integrable
   functions with summable `L¹` norms can be integrated termwise (Mathlib: `MeasureTheory.integral_tsum`-type or
   `hasSum_integral_of_summable_integral_norm`); the same bound gives the two summability claims of the statement
   (`‖pairE x μ w‖ ≤ (1/2π) ∫ ‖pairK‖`).
5. Hypotheses to check for step 3: zeros of ξ have `0 < Re ρ < 1 < c` (stub `xiZeta_zero_re_mem`), are `≠ 0`, and
   `ρ + μ ≠ 0` because `μ` is real with `μ > 0` or `μ < -1` while `0 < Re ρ < 1`; for `τ_k`: `Re τ_k < 0 < c`, `τ_k ≠ 0`, and
   `τ_k + μ ≠ 0` is the hypothesis `hne`; for `w = 1`: `1 + μ ≠ 0`.
The result is exactly the stated identity, with `pairE x μ 1` from `w = 1`.
