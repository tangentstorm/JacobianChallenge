import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfMfderivId
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Basic

/-!
# Sufficient condition: `c.symm =ᶠ[𝓝 e] id` discharges the bridge hypothesis

For a chart `c : OpenPartialHomeomorph E E` on the model space
itself, if its inverse agrees with the identity in a neighborhood
of `e`, then the corrected chart-pullback at `e` coincides with the
provisional chart-form. Reduces to the previous-tick bridge via
`Filter.EventuallyEq.mfderiv_eq` + `mfderiv_id`. Useful for the
self-chart case (translation charts on the torus model `ℂ`).
-/

namespace JacobianChallenge.Periods

open Filter Topology JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/--
For a self-chart `c : OpenPartialHomeomorph E E`, if `c.symm`
agrees with the identity on a neighborhood of `e`, the corrected
chart-pullback at `e` coincides with the provisional chart-form.
-/
theorem chartedFormPullback_eq_chartedForm_of_symm_eventuallyEq_id
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E) (e : E)
    (h : (fun x : E => c.symm x) =ᶠ[𝓝 e] id) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [h.mfderiv_eq]
  exact mfderiv_id

end JacobianChallenge.Periods
