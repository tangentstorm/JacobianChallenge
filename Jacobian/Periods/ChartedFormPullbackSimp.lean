import Jacobian.Periods.ChartedFormPullback
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormPullback` of the zero form is zero. -/
@[simp] theorem chartedFormPullback_zero
    (c : OpenPartialHomeomorph X E) :
    chartedFormPullback c (0 : HolomorphicOneForm E X) = 0 := by
  funext e
  convert ContinuousLinearMap.zero_comp _

/-- `chartedFormPullback` distributes over negation. -/
@[simp] theorem chartedFormPullback_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormPullback c (-ω) = -chartedFormPullback c ω := by
  funext e
  convert ContinuousLinearMap.neg_comp _ _
  infer_instance

/-- `chartedFormPullback` distributes over addition. -/
@[simp] theorem chartedFormPullback_add
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormPullback c (ω + η) = chartedFormPullback c ω + chartedFormPullback c η := by
  funext e
  convert ContinuousLinearMap.add_comp _ _ _
  infer_instance

end JacobianChallenge.Periods
