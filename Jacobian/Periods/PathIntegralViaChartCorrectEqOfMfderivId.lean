import Jacobian.Periods.PathLift
import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralInChartCorrectEqOfMfderivId

/-!
# `pathIntegralViaChartCorrect = pathIntegralViaChart` when `mfderiv c.symm = id`

Lifts the in-chart bridge to the from-`X` via-chart layer. Both
sides differ only in their use of `chartedFormPullback` vs
`chartedForm`; under the global `mfderiv c.symm = id` hypothesis
they coincide.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- If `mfderiv c.symm` is identity everywhere on `E`, the corrected
from-`X` chart-local integral coincides with the provisional one. -/
theorem pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_mfderiv_id
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source)
    (hd : ∀ e, mfderiv (modelWithCornersSelf ℂ E)
                      (modelWithCornersSelf ℂ E) c.symm e =
               ContinuousLinearMap.id ℂ E) :
    pathIntegralViaChartCorrect c ω γ h =
      pathIntegralViaChart c ω γ h := by
  unfold pathIntegralViaChartCorrect pathIntegralViaChart
  exact pathIntegralInChartCorrect_eq_pathIntegralInChart_of_mfderiv_id
    c ω (chartLift c γ h) hd

end JacobianChallenge.Periods
