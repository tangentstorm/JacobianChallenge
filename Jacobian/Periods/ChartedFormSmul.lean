import Jacobian.Periods.ChartedForm
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedForm` is ℂ-linear in the form. -/
@[simp] theorem chartedForm_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) :
    chartedForm c (k • ω) = k • chartedForm c ω := by
  funext e
  show ((k • ω : HolomorphicOneForm E X) : ∀ x, _) (c.symm e) =
       (k • chartedForm c ω) e
  rw [ContMDiffSection.coe_smul]
  rfl

end JacobianChallenge.Periods
