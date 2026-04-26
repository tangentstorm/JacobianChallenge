import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartLinear

/-!
# Negate-and-reverse equals self (provisional in-chart)

Provisional in-chart analogue of `pathIntegralInChartCorrect_neg_symm_eq_self`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
`pathIntegralInChart c (-ω) γ.symm = pathIntegralInChart c ω γ`.

Uses the simpler `chartedForm` (which drops the `mfderiv` factor).
Proof: `_symm` then `_neg` then `neg_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse cancellation (provisional in-chart):
`∫(-ω, γ.symm) = ∫(ω, γ)`. -/
theorem pathIntegralInChart_neg_symm_eq_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-ω) γ.symm =
      pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_symm, pathIntegralInChart_neg, neg_neg]

end JacobianChallenge.Periods
