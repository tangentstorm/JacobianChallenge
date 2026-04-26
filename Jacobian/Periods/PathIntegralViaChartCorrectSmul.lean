import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectSmul

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The from-`X` corrected chart-local path integral is ℂ-linear
in the form. -/
@[simp] theorem pathIntegralViaChartCorrect_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (k • ω) γ h =
      k • pathIntegralViaChartCorrect c ω γ h := by
  unfold pathIntegralViaChartCorrect
  exact pathIntegralInChartCorrect_smul c k ω _

end JacobianChallenge.Periods
