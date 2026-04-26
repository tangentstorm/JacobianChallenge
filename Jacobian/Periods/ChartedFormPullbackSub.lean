import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackSimp

/-!
# Subtraction linearity of `chartedFormPullback`

Derives `chartedFormPullback c (ω - η) = chartedFormPullback c ω - chartedFormPullback c η`
from the existing `_add` and `_neg` lemmas. At this level (function
equation on `E → E →L[ℂ] ℂ`) `_add` is unconditional, so `_sub` is
also unconditional — unlike the integrated versions, which need
`CurveIntegrable` for `_add`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `chartedFormPullback` distributes over subtraction. -/
@[simp] theorem chartedFormPullback_sub
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) :
    chartedFormPullback c (ω - η) =
      chartedFormPullback c ω - chartedFormPullback c η := by
  rw [sub_eq_add_neg, sub_eq_add_neg, chartedFormPullback_add,
      chartedFormPullback_neg]

end JacobianChallenge.Periods
