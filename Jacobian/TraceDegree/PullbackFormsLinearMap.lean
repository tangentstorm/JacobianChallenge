import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunSmul

/-!
# Pullback of holomorphic 1-forms as a ℂ-linear map

Bundles `pullbackFormsFun` as a `ℂ`-linear map using the linearity
lemmas `pullbackFormsFun_add` and `pullbackFormsFun_smul`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]


noncomputable def pullbackFormsLinearMap (f : X → Y) :
    HolomorphicOneForm E Y →ₗ[ℂ] (X → E →L[ℂ] ℂ) where
  toFun η := pullbackFormsFun f η
  map_add' η ζ := pullbackFormsFun_add f η ζ
  map_smul' k η := pullbackFormsFun_smul f k η

/--
Sanity simp: applying the bundled linear map equals the underlying
pullback function.
-/
@[simp] theorem pullbackFormsLinearMap_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f η = pullbackFormsFun f η := rfl

end JacobianChallenge.TraceDegree
