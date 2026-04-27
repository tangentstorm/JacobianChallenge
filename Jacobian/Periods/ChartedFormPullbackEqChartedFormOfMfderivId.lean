import Jacobian.Periods.ChartedFormPullbackEqChartedFormCompMfderiv

/-!
# `chartedFormPullback = chartedForm` when `mfderiv c.symm` is the identity

If the manifold derivative of `c.symm` at `e` is the identity
continuous linear map (which happens for translation-transition
charts on `ℂ` itself, e.g. the torus example), then the corrected
chart-pullback coincides with the provisional chart-form. This is
the precise hypothesis under which the provisional layer is exactly
correct.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Conditional bridge: if `mfderiv c.symm e` is the identity CLM,
the corrected chart-pullback at `e` equals the provisional chart-form
at `e`. -/
theorem chartedFormPullback_eq_chartedForm_of_mfderiv_id
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E)
    (h : mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e =
         ContinuousLinearMap.id ℂ E) :
    chartedFormPullback c ω e = chartedForm c ω e := by
  rw [chartedFormPullback_eq_chartedForm_comp_mfderiv, h]
  exact ContinuousLinearMap.comp_id _

/-- Vector-apply form: if `mfderiv c.symm e v = v`, the corrected
chart-pullback applied to `(e, v)` equals the provisional chart-form
applied to `(e, v)`. Strictly weaker hypothesis than the full
identity equation, since only one tangent direction is required. -/
theorem chartedFormPullback_apply_eq_chartedForm_apply_of_mfderiv_id_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e v : E)
    (h : mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e v = v) :
    chartedFormPullback c ω e v = chartedForm c ω e v := by
  rw [chartedFormPullback_apply_eq_chartedForm_apply_mfderiv, h]

/-- Function-equality form: under the global mfderiv-identity
hypothesis, the corrected chart-pullback function equals the
provisional chart-form function on all of `E`. -/
theorem chartedFormPullback_eq_chartedForm_of_mfderiv_id'
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (h : ∀ e, mfderiv (modelWithCornersSelf ℂ E)
                     (modelWithCornersSelf ℂ E) c.symm e =
              ContinuousLinearMap.id ℂ E) :
    chartedFormPullback c ω = chartedForm c ω := by
  funext e
  exact chartedFormPullback_eq_chartedForm_of_mfderiv_id c ω e (h e)

end JacobianChallenge.Periods
