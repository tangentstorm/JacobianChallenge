import Jacobian.Periods.ChartedFormPullback

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem chartedFormPullback_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c ω e =
      (ω.toFun (c.symm e)).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e) := rfl

/-- Applying `chartedFormPullback` at a chart point and then at a
tangent vector gives the explicit chain-rule formula. -/
@[simp] theorem chartedFormPullback_apply_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e : E) (v : E) :
    chartedFormPullback c ω e v =
      ω.toFun (c.symm e)
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e v) := rfl

end JacobianChallenge.Periods
