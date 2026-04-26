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

/-- Applying the bundled chart-pullback at a chart point and then at
a tangent vector gives the explicit chain-rule formula. -/
@[simp] theorem chartedFormPullbackLinearMap_apply_vec
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e : E) (v : E) :
    chartedFormPullbackLinearMap c ω e v =
      ω.toFun (c.symm e)
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e v) := rfl

end JacobianChallenge.Periods
