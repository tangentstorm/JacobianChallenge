import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.ChartedFormSmul

/-!
# Bundled `chartedForm` as a ℂ-linear map (provisional)

Provisional analogue of `ChartedFormPullbackLinearMap.lean` at the
corrected layer. Packages the unbundled `chartedForm c` (which drops
the `mfderiv` factor) as a `ℂ`-linear map at the function level.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Provisional chart-form, packaged as a ℂ-linear map at the
function level. -/
noncomputable def chartedFormLinearMap
    (c : OpenPartialHomeomorph X E) :
    HolomorphicOneForm E X →ₗ[ℂ] (E → E →L[ℂ] ℂ) where
  toFun ω := chartedForm c ω
  map_add' ω η := chartedForm_add c ω η
  map_smul' k ω := chartedForm_smul c k ω

/-- Sanity simp: applying the bundled linear map equals the underlying
provisional chart-form. -/
@[simp] theorem chartedFormLinearMap_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormLinearMap c ω = chartedForm c ω := rfl

end JacobianChallenge.Periods
