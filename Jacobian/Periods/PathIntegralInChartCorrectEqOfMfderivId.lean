import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfMfderivId

/-!
# `pathIntegralInChartCorrect = pathIntegralInChart` when `mfderiv c.symm = id`

If the manifold derivative of `c.symm` is the identity continuous
linear map at every point of the model space `E`, then the corrected
chart-local integral coincides with the provisional chart-local
integral. This is the precise hypothesis under which the provisional
integration layer is exactly correct (e.g. translation-transition
charts on `ℂ`, as used in the torus example).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
If `mfderiv c.symm` is everywhere the identity CLM, the
corrected chart-local integral equals the provisional one.
-/
theorem pathIntegralInChartCorrect_eq_pathIntegralInChart_of_mfderiv_id
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (h : ∀ e, mfderiv (modelWithCornersSelf ℂ E)
                     (modelWithCornersSelf ℂ E) c.symm e =
              ContinuousLinearMap.id ℂ E) :
    pathIntegralInChartCorrect c ω γ =
      pathIntegralInChart c ω γ := by
  show curveIntegral (chartedFormPullback c ω) γ =
       curveIntegral (chartedForm c ω) γ
  congr 1
  funext e
  exact chartedFormPullback_eq_chartedForm_of_mfderiv_id c ω e (h e)

end JacobianChallenge.Periods
