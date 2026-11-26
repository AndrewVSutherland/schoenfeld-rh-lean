## Your assignment: NAME = p4
Owned file: SchoenfeldRH/Base/Digamma.lean (3 statements and the definition `realDigamma`, which you must not change),
helper dir SchoenfeldRH/Lemmas/p4/. To be proved from Mathlib alone.
Mathematical notes from the lead (use or ignore):
- `Complex.digamma` is Mathlib's logarithmic derivative of `Complex.Gamma` (Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean
  or nearby: grep for `digamma`). Mathlib has the recurrence `ψ(z + 1) = ψ(z) + 1/z` and `ψ(1) = -γ`.
- Series: `ψ(w) - ψ(1) = Σ_{k≥0} (1/(k+1) - 1/(k+w))`. One route: the recurrence gives the partial sums exactly,
  `Σ_{k<N} (1/(k+1) - 1/(k+w)) = (ψ(1+N) - ψ(1)) - (ψ(w+N) - ψ(w))`, so it remains to show `ψ(w+N) - ψ(1+N) → 0`; this
  can be obtained from the Euler/Gauss limit formula for Γ in Mathlib (`Complex.GammaSeq`), from a product formula, or from
  convexity estimates on the real axis combined with analyticity. Choose what Mathlib supports best.
- Real axis: Γ is real and positive on positive reals, so ψ is real there. `log Γ` is convex on `(0, ∞)`
  (`Real.convexOn_log_Gamma`) and `log Γ(x+1) - log Γ(x) = log x`; comparing the derivative of a convex function with
  the slopes of the secants over `[x-1, x]` and `[x, x+1]` gives `log (x-1) ≤ ψ(x) ≤ log x` for `x > 1`.
