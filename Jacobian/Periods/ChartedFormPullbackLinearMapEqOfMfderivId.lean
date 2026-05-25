import Jacobian.Periods.ChartedFormPullbackLinearMap
import Jacobian.Periods.ChartedFormLinearMap
import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfMfderivId

/-!
# Bundled-LinearMap bridge under `mfderiv c.symm = id`

When the manifold derivative of `c.symm` is the identity at every
point of `E`, the bundled `chartedFormPullbackLinearMap c` coincides
with the bundled `chartedFormLinearMap c` as ℂ-linear maps.

This is the bundle-level companion of
`chartedFormPullback_eq_chartedForm_of_mfderiv_id`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Bundled-LinearMap bridge: under the global `mfderiv c.symm = id`
hypothesis, the corrected and provisional bundled chart-form
LinearMaps are equal.
-/
theorem chartedFormPullbackLinearMap_eq_chartedFormLinearMap_of_mfderiv_id
    (c : OpenPartialHomeomorph X E)
    (hd : ∀ e, mfderiv (modelWithCornersSelf ℂ E)
                       (modelWithCornersSelf ℂ E) c.symm e =
               ContinuousLinearMap.id ℂ E) :
    chartedFormPullbackLinearMap c = chartedFormLinearMap c := by
  refine LinearMap.ext fun ω => ?_
  funext e
  exact chartedFormPullback_eq_chartedForm_of_mfderiv_id c ω e (hd e)

end JacobianChallenge.Periods
