import SchoenfeldRH.Xi.Basic

/-!
# The zero sum `W(B)`

`Complex.riemannXi s = s (s - 1) π^(-s/2) Γ(s/2) ζ(s) / 2` is the entire function defined in the vendored
PrimeNumberTheoremAnd module `Mathlib/Analysis/SpecialFunctions/CompletedXi.lean`; its zeros are the nontrivial
zeros of `ζ`, with the same multiplicities.
`zeroSumW B = Σ_ρ m_ρ / (|ρ| · |B + 1/2 - ρ|)`, the sum over the zeros `ρ` of `riemannXi` with multiplicity `m_ρ`.
Under the Riemann hypothesis `ρ = 1/2 + iγ` and the summand is `m_ρ / √((1/4 + γ²)(B² + γ²))`.
-/

namespace SchoenfeldRH

open Complex


/-- `W(B) = Σ_ρ m_ρ / (‖ρ‖ · ‖B + 1/2 - ρ‖)` over the zeros of `riemannXi`, with multiplicity. -/
noncomputable def zeroSumW (B : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
    (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)

end SchoenfeldRH
