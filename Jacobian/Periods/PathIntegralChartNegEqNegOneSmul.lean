import Jacobian.Periods.PathIntegralChartLinear

/-!
# Form negation as scalar multiplication by `-1` (provisional in-chart)

Provisional in-chart layer of `_neg_eq_neg_one_smul`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form negation equals `(-1) •` on the integral
(provisional in-chart). -/
theorem pathIntegralInChart_neg_eq_neg_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-ω) γ =
      (-1 : ℂ) • pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_neg, neg_one_smul]

end JacobianChallenge.Periods
