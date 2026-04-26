import Jacobian.Periods.PathIntegralViaChartCorrect

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The from-`X` corrected chart-local path integral unfolds to
`pathIntegralInChartCorrect` on the chart-lifted path. -/
@[simp]
theorem pathIntegralViaChartCorrect_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ h =
      pathIntegralInChartCorrect c ω (chartLift c γ h) := rfl

end JacobianChallenge.Periods
