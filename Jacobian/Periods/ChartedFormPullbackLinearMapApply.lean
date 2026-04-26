import Jacobian.Periods.ChartedFormPullbackLinearMap

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The bundled chart-pullback evaluated at a point. -/
@[simp] theorem chartedFormPullbackLinearMap_apply_at
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullbackLinearMap c ω e = chartedFormPullback c ω e := rfl

end JacobianChallenge.Periods
