## Your assignment: NAME = p3
Owned file: SchoenfeldRH/Base/Hadamard.lean (1 statement: `hadamard_logDeriv`), helper dir SchoenfeldRH/Lemmas/p3/.
To be proved from Mathlib and the in-tree library `PrimeNumberTheoremAnd` (directory WORKSPACE/PrimeNumberTheoremAnd,
Apache-2.0, by M. Cipollina, from the PrimeNumberTheoremAnd project): it proves the Hadamard factorization theorem for entire
functions of finite order (PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization*.lean and the files they
import; namespace `Complex.Hadamard`). Read those files: they are your main tool. You will need to add the right
`import PrimeNumberTheoremAnd....` lines to your file.
The library is already built in your workspace (it compiles unchanged at this Lean/Mathlib version); do not edit files
under PrimeNumberTheoremAnd/.
Mathematical notes from the lead (use or ignore):
- With `f` entire of order ≤ 1 and `f 0 ≠ 0`, Hadamard gives `f(z) = exp(a + b z) ∏_ρ (1 - z/ρ) exp(z/ρ)` over the zeros with
  multiplicity, and `Σ 1/|ρ|^(1+ε) < ∞`. Taking the logarithmic derivative termwise gives
  `f'/f(z) = b + Σ_ρ (1/(z - ρ) + 1/ρ)`.
- The library indexes zeros with multiplicity by a type (`divisorZeroIndex₀`); the statement here uses the subtype
  `{ρ // f ρ = 0}` weighted by `analyticOrderNatAt f ρ`. Converting a sum over the former into a weighted sum over the
  latter (grouping the fibres of the map "index ↦ zero", each of size the multiplicity) is part of the work.
- The growth hypothesis `‖f z‖ ≤ C exp (C ‖z‖ log (‖z‖ + 2))` has to be turned into the library's notion of finite order
  (order ≤ 1, or ≤ 1 + ε for every ε).
