import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Chart-pullback of holomorphic 1-forms along an open partial
homeomorphism, packaged as a ℂ-linear map at the function level.
-/
noncomputable def chartedFormPullbackLinearMap
    (c : OpenPartialHomeomorph X E) :
    HolomorphicOneForm E X →ₗ[ℂ] (E → E →L[ℂ] ℂ) where
  toFun ω := chartedFormPullback c ω
  map_add' ω η := chartedFormPullback_add c ω η
  map_smul' k ω := chartedFormPullback_smul c k ω

/--
Sanity simp: applying the bundled linear map equals the underlying
chart pullback.
-/
@[simp] theorem chartedFormPullbackLinearMap_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormPullbackLinearMap c ω = chartedFormPullback c ω := rfl

end JacobianChallenge.Periods
