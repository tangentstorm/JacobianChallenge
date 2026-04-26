import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectLinear

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The from-`X` corrected chart-local path integral negates with
the form. -/
@[simp] theorem pathIntegralViaChartCorrect_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (-ω) γ h =
      - pathIntegralViaChartCorrect c ω γ h := by
  unfold pathIntegralViaChartCorrect
  exact pathIntegralInChartCorrect_neg c ω _

end JacobianChallenge.Periods
