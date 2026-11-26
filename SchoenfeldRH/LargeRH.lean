import SchoenfeldRH.Explicit
import SchoenfeldRH.ZeroSum.Bound
import SchoenfeldRH.Large

/-!
# RH implies Schoenfeld's bound for `x ≥ 30000`

Assembly of the three analytic inputs: the smoothed explicit formulas (`SchoenfeldRH.Explicit`), the bound for the zero
sum `zeroSumW` (`SchoenfeldRH.ZeroSum.Bound`), and the final inequality (`SchoenfeldRH.Large`).
-/

namespace SchoenfeldRH

/-- Under the Riemann hypothesis, `|ψ(x) - x| < √x (log x)² / (8π)` for all real `x ≥ 30000`. -/
theorem schoenfeld_large_of_RH (hRH : RiemannHypothesis) (x : ℝ) (hx : 30000 ≤ x) :
    |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) :=
  schoenfeld_large_of_contracts zeroSumW
    (fun n lam hn hlam => psi_sub_le_of_RH hRH n hn lam hlam)
    (fun n lam hn hlam hne => sub_psi_le_of_RH hRH n hn lam hlam hne)
    (fun B hB => zeroSumW_le_of_RH hRH B hB)
    zeroSumW_nonneg x hx

end SchoenfeldRH
