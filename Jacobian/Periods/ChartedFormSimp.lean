import Jacobian.Periods.ChartedForm
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedForm` distributes over negation. -/
@[simp] theorem chartedForm_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedForm c (-ω) = -chartedForm c ω := by
  funext e
  show ((-ω : HolomorphicOneForm E X) : ∀ x, _) (c.symm e) = -chartedForm c ω e
  rw [ContMDiffSection.coe_neg]
  rfl

/-- `chartedForm` distributes over addition. -/
@[simp] theorem chartedForm_add
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedForm c (ω + η) = chartedForm c ω + chartedForm c η := by
  funext e
  show ((ω + η : HolomorphicOneForm E X) : ∀ x, _) (c.symm e) = (chartedForm c ω + chartedForm c η) e
  rw [ContMDiffSection.coe_add]
  rfl

end JacobianChallenge.Periods
