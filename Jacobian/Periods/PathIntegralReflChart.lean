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

set_option linter.unusedSectionVars false in
/-- The provisional chart-form on the refl chart is just `ω.toFun`. -/
theorem chartedForm_refl_apply
    (ω : HolomorphicOneForm E E) (e : E) :
    chartedForm (OpenPartialHomeomorph.refl E) ω e = ω.toFun e := rfl

set_option linter.unusedSectionVars false in
/-- The corrected chart-pullback on the refl chart is just `ω.toFun`
(the `mfderiv` factor is the identity). -/
theorem chartedFormPullback_refl_apply
    (ω : HolomorphicOneForm E E) (e : E) :
    chartedFormPullback (OpenPartialHomeomorph.refl E) ω e = ω.toFun e := by
  rw [chartedFormPullback_refl_eq_chartedForm_refl, chartedForm_refl_apply]

set_option linter.unusedSectionVars false in
/-- The provisional in-chart integral on the refl chart is just the
direct curve integral of `ω.toFun`. (Disambiguated from the
existing `pathIntegralInChart_refl`, which is for constant paths.) -/
theorem pathIntegralInChart_reflChart
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b) :
    pathIntegralInChart (OpenPartialHomeomorph.refl E) ω γ =
      curveIntegral ω.toFun γ := by
  show curveIntegral (chartedForm (OpenPartialHomeomorph.refl E) ω) γ =
       curveIntegral ω.toFun γ
  rfl

set_option linter.unusedSectionVars false in
/-- The provisional via-chart integral on the refl chart equals the
direct curve integral of `ω.toFun`. -/
theorem pathIntegralViaChart_reflChart
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (OpenPartialHomeomorph.refl E).source) :
    pathIntegralViaChart (OpenPartialHomeomorph.refl E) ω γ h =
      curveIntegral ω.toFun γ := by
  unfold pathIntegralViaChart
  exact pathIntegralInChart_reflChart ω _

set_option linter.unusedSectionVars false in
/-- Corrected in-chart integral on the refl chart equals the direct
`curveIntegral ω.toFun γ`. Combines the refl bridge with the
provisional formula. -/
theorem pathIntegralInChartCorrect_reflChart
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect (OpenPartialHomeomorph.refl E) ω γ =
      curveIntegral ω.toFun γ := by
  rw [pathIntegralInChartCorrect_refl_eq_pathIntegralInChart_refl,
      pathIntegralInChart_reflChart]

set_option linter.unusedSectionVars false in
/-- Corrected via-chart integral on the refl chart equals the direct
`curveIntegral ω.toFun γ`. -/
theorem pathIntegralViaChartCorrect_reflChart
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (OpenPartialHomeomorph.refl E).source) :
    pathIntegralViaChartCorrect (OpenPartialHomeomorph.refl E) ω γ h =
      curveIntegral ω.toFun γ := by
  rw [pathIntegralViaChartCorrect_refl_eq_pathIntegralViaChart_refl,
      pathIntegralViaChart_reflChart]

set_option linter.unusedSectionVars false in
/-- Function-level: the provisional chart-form on the refl chart is
literally the underlying form's `toFun`. -/
theorem chartedForm_refl_eq_toFun
    (ω : HolomorphicOneForm E E) :
    chartedForm (OpenPartialHomeomorph.refl E) ω = ω.toFun := rfl

set_option linter.unusedSectionVars false in
/-- Function-level: the corrected chart-pullback on the refl chart
is the underlying form's `toFun` (mfderiv factor cancels). -/
theorem chartedFormPullback_refl_eq_toFun
    (ω : HolomorphicOneForm E E) :
    chartedFormPullback (OpenPartialHomeomorph.refl E) ω = ω.toFun := by
  funext e
  exact chartedFormPullback_refl_apply ω e

end JacobianChallenge.Periods
