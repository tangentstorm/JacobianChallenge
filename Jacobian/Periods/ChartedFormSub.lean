import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormSimp

/-!
# Subtraction linearity of `chartedForm`

Derives `chartedForm c (ω - η) = chartedForm c ω - chartedForm c η`
from the existing `_add` and `_neg` lemmas. Mirrors
`ChartedFormPullbackSub.lean` at the corrected layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedForm` distributes over subtraction. -/
@[simp] theorem chartedForm_sub
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedForm c (ω - η) = chartedForm c ω - chartedForm c η := by
  rw [sub_eq_add_neg, sub_eq_add_neg, chartedForm_add, chartedForm_neg]

end JacobianChallenge.Periods
