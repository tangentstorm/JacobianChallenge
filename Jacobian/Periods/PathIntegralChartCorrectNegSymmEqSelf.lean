import Jacobian.Periods.PathIntegralChartCorrectSimp
import Jacobian.Periods.PathIntegralChartCorrectLinear

/-!
# Negate-and-reverse equals self (in-chart, corrected)

In-chart corrected analogue of `pathIntegralViaChartCorrect_neg_symm_eq_self`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
`pathIntegralInChartCorrect c (-ω) γ.symm = pathIntegralInChartCorrect c ω γ`.

Proof: `_symm` then `_neg` then `neg_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse cancellation (in-chart corrected):
`∫(-ω, γ.symm) = ∫(ω, γ)`. -/
theorem pathIntegralInChartCorrect_neg_symm_eq_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-ω) γ.symm =
      pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_symm, pathIntegralInChartCorrect_neg, neg_neg]

end JacobianChallenge.Periods
