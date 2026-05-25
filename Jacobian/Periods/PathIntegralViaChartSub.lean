import Jacobian.Periods.PathLift
import Jacobian.Periods.PathIntegralChartSub

/-!
# Conditional subtraction linearity of the provisional `pathIntegralViaChart`

Lifts `pathIntegralInChart_sub_of_curveIntegrable` across the
chart-lift wrapper. Mirrors `PathIntegralViaChartCorrectSub.lean`
at the corrected layer.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional subtraction linearity of the provisional from-`X`
chart-local path integral.
-/
theorem pathIntegralViaChart_sub_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source)
    (hω : CurveIntegrable (chartedForm c ω) (chartLift c γ h))
    (hη : CurveIntegrable (chartedForm c η) (chartLift c γ h)) :
    pathIntegralViaChart c (ω - η) γ h =
      pathIntegralViaChart c ω γ h - pathIntegralViaChart c η γ h := by
  unfold pathIntegralViaChart
  exact pathIntegralInChart_sub_of_curveIntegrable c ω η _ hω hη

end JacobianChallenge.Periods
