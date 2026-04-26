import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectZero

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The from-`X` corrected chart-local path integral of the zero form is zero. -/
@[simp] theorem pathIntegralViaChartCorrect_zero
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (0 : HolomorphicOneForm E X) γ h = 0 := by
  unfold pathIntegralViaChartCorrect
  exact pathIntegralInChartCorrect_zero _ _

end JacobianChallenge.Periods
