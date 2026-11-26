## Your assignment: NAME = p5
Owned file: SchoenfeldRH/ZeroSum/Basic.lean (13 statements), helper dir SchoenfeldRH/Lemmas/p5/.
You may use, as black boxes, the statements (stubs of other provers) in SchoenfeldRH/Base/Xi.lean, Base/Constants.lean,
Base/Growth.lean, Base/Hadamard.lean, and the definitions in Base/XiDef.lean and ZeroSum/Defs.lean (`zeroSumW`).
Mathematical notes from the lead (use or ignore). ξ = `xiZeta`; zeros ρ range over `{ρ // xiZeta ρ = 0}` with
multiplicity `m_ρ = analyticOrderNatAt xiZeta ρ`:
- `xiZeta_zero_re_of_RH`: a zero of ξ lies in the open strip (stub `xiZeta_zero_re_mem`) and is a zero of ζ
  (`xiZeta_eq` and the non-vanishing of the Gamma factor; `riemannZeta` vs `completedRiemannZeta`: Mathlib has
  `riemannZeta_def_of_ne_zero`), not a trivial zero and not 1, so Mathlib's `RiemannHypothesis` gives `Re ρ = 1/2`.
- `hasSum_hadamard_xiZeta`: apply the stub `hadamard_logDeriv` to ξ (`differentiable_xiZeta`, `xiZeta_zero`,
  `xiZeta_growth`); evaluating at `z = 0` (where every term `1/(0 - ρ) + 1/ρ` vanishes) identifies the constant
  `b = ξ'/ξ(0)`.
- `hasSum_zero_inv_norm_sq` (under RH): the functional equation `ξ(1 - s) = ξ(s)` (from Mathlib's functional equation for
  the completed zeta function) gives `ξ'/ξ(1) = -ξ'/ξ(0)`; the Hadamard sum at `s = 1`, with `1 - ρ = conj ρ` under RH,
  gives `Σ m_ρ/|ρ|² = -2 ξ'/ξ(0)`, and `ξ'(0) = -Λ₀(0)`, `ξ'(1) = Λ₀(1)` (stubs) with the value of `Re (2 Λ₀(1))` (stub).
  The bound `≤ 1/20` is the stub `two_add_eulerMascheroni_sub_log_lt`.
- `hasSum_poisson` (under RH): real parts of the Hadamard sum at the real point `s = β + 1/2`:
  `Re 1/(s - ρ) = β/(β² + γ²)`, `Re 1/ρ = (1/2)/|ρ|²`, and the previous item.
- `summable_zeroSumW`: under RH the term is `m/√((1/4+γ²)(B²+γ²)) ≤ max(1, 1/(2B))·m/|ρ|²`-type comparison with the
  summable family `m/|ρ|²`.
