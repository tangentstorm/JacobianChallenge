import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfMfderivId
import Jacobian.Periods.MfderivTranslation
import Mathlib.Topology.Basic

/-!
# Translation-chart instance: corrected and provisional pullbacks coincide

If a self-chart `c : OpenPartialHomeomorph E E` has `c.symm` equal
(as a function) to a translation `x ↦ x + v` (or `x ↦ v + x`), then
the corrected chart-pullback coincides with the provisional
chart-form unconditionally. Translations have identity manifold
derivative, so the previous-tick `_of_mfderiv_id` bridge applies.

This is the second concrete bridge instance after the refl chart,
and the one most directly relevant to the complex torus (transition
charts on `ℂ` are translations by lattice elements).
-/

namespace JacobianChallenge.Periods

open Filter Topology JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/--
Translation-chart bridge (right form): if `c.symm = fun x => x + v`,
the corrected chart-pullback equals the provisional chart-form
unconditionally.
-/
theorem chartedFormPullback_eq_chartedForm_of_symm_eq_add_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E) (h : (fun x : E => c.symm x) = (fun x : E => x + v)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [show ((c.symm : E → E)) = (fun x => x + v) from h]
  exact mfderiv_add_const_self v e

/--
Translation-chart bridge (left form): if `c.symm = fun x => v + x`,
the corrected chart-pullback equals the provisional chart-form
unconditionally.
-/
theorem chartedFormPullback_eq_chartedForm_of_symm_eq_const_add
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E) (h : (fun x : E => c.symm x) = (fun x : E => v + x)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [show ((c.symm : E → E)) = (fun x => v + x) from h]
  exact mfderiv_const_add_self v e

/--
Translation-chart bridge (subtraction form): if `c.symm =
fun x => x - v`, the corrected chart-pullback equals the provisional
chart-form unconditionally.
-/
theorem chartedFormPullback_eq_chartedForm_of_symm_eq_sub_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E) (h : (fun x : E => c.symm x) = (fun x : E => x - v)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [show ((c.symm : E → E)) = (fun x => x - v) from h]
  exact mfderiv_sub_const_self v e

/--
EventuallyEq variant of the right-translation bridge: if
`c.symm =ᶠ[𝓝 e] (fun x => x + v)`, the corrected chart-pullback at
`e` coincides with the provisional chart-form. Weaker than global
function equality — only the local neighborhood of `e` matters for
`mfderiv`.
-/
theorem chartedFormPullback_eq_chartedForm_of_symm_eventuallyEq_add_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E)
    (h : (fun x : E => c.symm x) =ᶠ[𝓝 e] (fun x : E => x + v)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [h.mfderiv_eq]
  exact mfderiv_add_const_self v e

/-- EventuallyEq variant of the left-translation bridge. -/
theorem chartedFormPullback_eq_chartedForm_of_symm_eventuallyEq_const_add
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E)
    (h : (fun x : E => c.symm x) =ᶠ[𝓝 e] (fun x : E => v + x)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [h.mfderiv_eq]
  exact mfderiv_const_add_self v e

/-- EventuallyEq variant of the subtraction-translation bridge. -/
theorem chartedFormPullback_eq_chartedForm_of_symm_eventuallyEq_sub_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    (e v : E)
    (h : (fun x : E => c.symm x) =ᶠ[𝓝 e] (fun x : E => x - v)) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  apply chartedFormPullback_eq_chartedForm_of_mfderiv_id
  rw [h.mfderiv_eq]
  exact mfderiv_sub_const_self v e

end JacobianChallenge.Periods
