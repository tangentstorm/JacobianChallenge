import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfSymmEventuallyEqId
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Identity-chart instance: corrected and provisional pullbacks coincide

For the identity self-chart `OpenPartialHomeomorph.refl E`, the
corrected chart-pullback equals the provisional chart-form
unconditionally (the chart's inverse IS the identity, so the
`mfderiv c.symm = id` hypothesis is automatic).

This is the cleanest concrete witness that the bridge ladder fires
on a real chart.
-/

namespace JacobianChallenge.Periods

open Filter Topology JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/--
For the identity self-chart on `E`, the corrected chart-pullback
coincides with the provisional chart-form. Discharges the bridge
hypothesis directly via `OpenPartialHomeomorph.refl_symm` and
`refl_apply`.
-/
theorem chartedFormPullback_refl_eq_chartedForm_refl
    (ω : HolomorphicOneForm E E) (e : E) :
    chartedFormPullback (OpenPartialHomeomorph.refl E) ω e =
      chartedForm (OpenPartialHomeomorph.refl E) ω e := by
  apply chartedFormPullback_eq_chartedForm_of_symm_eventuallyEq_id
  apply Filter.Eventually.of_forall
  intro x
  simp [OpenPartialHomeomorph.refl_symm]

end JacobianChallenge.Periods
