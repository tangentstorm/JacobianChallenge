import Jacobian.Periods.ChartedFormPullback
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormPullback` is ℂ-linear in the form. -/
@[simp] theorem chartedFormPullback_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) :
    chartedFormPullback c (k • ω) = k • chartedFormPullback c ω := by
  funext e
  convert ContinuousLinearMap.smul_comp _ _ _
  infer_instance

end JacobianChallenge.Periods
