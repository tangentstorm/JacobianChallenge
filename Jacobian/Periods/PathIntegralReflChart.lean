import Jacobian.Periods.ChartedFormPullbackRefl
import Jacobian.Periods.PathIntegralInChartCorrectEqOfMfderivId
import Jacobian.Periods.PathIntegralViaChartCorrectEqOfMfderivId
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Refl-chart instance: corrected and provisional integrals coincide

Lifts the previous-tick `chartedFormPullback_refl_eq_chartedForm_refl`
up the integration tower for the identity self-chart
`OpenPartialHomeomorph.refl E`. Each layer uses the global
`mfderiv (refl E).symm = id` witness, here packaged as
`mfderiv_refl_symm_eq_id`, to discharge the bridge hypothesis.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

set_option linter.unusedSectionVars false in
/-- Global witness: the manifold derivative of the refl chart's
inverse is the identity at every model-space point. -/
theorem mfderiv_refl_symm_eq_id (e : E) :
    mfderiv (modelWithCornersSelf ℂ E)
            (modelWithCornersSelf ℂ E)
            (OpenPartialHomeomorph.refl E).symm e =
      ContinuousLinearMap.id ℂ E := by
  have h : (fun x : E => (OpenPartialHomeomorph.refl E).symm x) = id := by
    funext x; simp [OpenPartialHomeomorph.refl_symm]
  rw [show ((OpenPartialHomeomorph.refl E).symm : E → E) = id from h]
  exact mfderiv_id

/-- In-chart corrected = provisional for the refl chart, on any
path in the model space. -/
theorem pathIntegralInChartCorrect_refl_eq_pathIntegralInChart_refl
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect (OpenPartialHomeomorph.refl E) ω γ =
      pathIntegralInChart (OpenPartialHomeomorph.refl E) ω γ :=
  pathIntegralInChartCorrect_eq_pathIntegralInChart_of_mfderiv_id _ _ _
    mfderiv_refl_symm_eq_id

/-- Via-chart corrected = provisional for the refl chart, on any
path whose range lies in `(refl E).source = univ`. -/
theorem pathIntegralViaChartCorrect_refl_eq_pathIntegralViaChart_refl
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (OpenPartialHomeomorph.refl E).source) :
    pathIntegralViaChartCorrect (OpenPartialHomeomorph.refl E) ω γ h =
      pathIntegralViaChart (OpenPartialHomeomorph.refl E) ω γ h :=
  pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_mfderiv_id _ _ _ _
    mfderiv_refl_symm_eq_id

set_option linter.unusedSectionVars false in
/-- For `chartedSpaceSelf E`, the chart at any point is the refl
chart, and its inverse has identity manifold derivative. -/
theorem mfderiv_chartAt_self_symm_eq_id (x e : E) :
    mfderiv (modelWithCornersSelf ℂ E)
            (modelWithCornersSelf ℂ E)
            (chartAt E x).symm e =
      ContinuousLinearMap.id ℂ E :=
  mfderiv_refl_symm_eq_id e

set_option linter.unusedSectionVars false in
/-- Lifting a path through the refl chart is the path itself
pointwise. -/
@[simp] theorem chartLift_refl_apply
    {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (OpenPartialHomeomorph.refl E).source)
    (t : unitInterval) :
    chartLift (OpenPartialHomeomorph.refl E) γ h t = γ t := rfl

end JacobianChallenge.Periods
