## Your assignment: NAME = p2
Owned file: SchoenfeldRH/Base/Growth.lean (1 statement: `xiZeta_growth`), helper dir SchoenfeldRH/Lemmas/p2/.
`xiZeta` is defined in SchoenfeldRH/Base/XiDef.lean (do not edit). To be proved from Mathlib alone. You may use, as black
boxes, the statements in SchoenfeldRH/Base/Xi.lean (another prover's stubs: `xiZeta_eq`, `xiZeta_zero`, `xiZeta_one`, ...)
if that helps, but a self-contained proof is preferable.
Mathematical notes from the lead (use or ignore):
- The claim is that ξ has order at most 1: `‖ξ(s)‖ ≤ C exp (C ‖s‖ log (‖s‖ + 2))` for all `s`.
- One route: `completedRiemannZeta₀` is defined in Mathlib as a Mellin transform (`WeakFEPair.Λ₀` of the even Hurwitz
  functional-equation pair at `a = 0`, see Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean and AbstractFuncEq.lean), of a
  function that decays rapidly at `∞` and is controlled at `0` by the functional equation. Bounding the Mellin integral
  directly gives `‖Λ₀(σ + it)‖ ≤ A^{|σ|+1} Γ(|σ| + B)`-type bounds, uniformly in `t`, which is of the required shape.
- Another route: for `Re s ≥ 2` use `ξ(s) = s (s - 1) π^(-s/2) Γ(s/2) ζ(s)` with `‖ζ(s)‖ ≤ ζ(2)` and
  `‖Γ(s/2)‖ ≤ Γ(Re s / 2)`; for `Re s ≤ -1` the functional equation `ξ(1 - s) = ξ(s)`; in the strip `-1 ≤ Re s ≤ 2` a
  Mellin integral is bounded uniformly in `Im s`.
- The constant `C` is not important; choose whatever is convenient.
