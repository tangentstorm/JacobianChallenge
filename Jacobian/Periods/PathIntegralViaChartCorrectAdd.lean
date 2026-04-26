import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectAdd

/-!
# Conditional addition linearity of `pathIntegralViaChartCorrect`

Lifts `pathIntegralInChartCorrect_add_of_curveIntegrable` across
the path-lift wrapper. Becomes unconditional once Packet F lands.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Conditional addition linearity of `pathIntegralViaChartCorrect`:
if both forms' chart pullbacks are curve-integrable along the lifted
path, the from-`X` chart-local integral distributes over addition. -/
theorem pathIntegralViaChartCorrect_add_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source)
    (hω : CurveIntegrable (chartedFormPullback c ω) (chartLift c γ h))
    (hη : CurveIntegrable (chartedFormPullback c η) (chartLift c γ h)) :
    pathIntegralViaChartCorrect c (ω + η) γ h =
      pathIntegralViaChartCorrect c ω γ h +
        pathIntegralViaChartCorrect c η γ h := by
  unfold pathIntegralViaChartCorrect
  exact pathIntegralInChartCorrect_add_of_curveIntegrable c ω η _ hω hη

end JacobianChallenge.Periods
