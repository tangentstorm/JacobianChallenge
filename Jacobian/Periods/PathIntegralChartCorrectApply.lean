import Jacobian.Periods.PathIntegralChartCorrect

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
The corrected chart-local path integral unfolds to `curveIntegral`
of `chartedFormPullback`.
-/
@[simp]
theorem pathIntegralInChartCorrect_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c ω γ =
      curveIntegral (chartedFormPullback c ω) γ := rfl

end JacobianChallenge.Periods
