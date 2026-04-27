import Jacobian.TraceDegree.PullbackFormsLinearMap
import Jacobian.TraceDegree.PullbackFunCompId

/-!
# Bundled-LinearMap pullback along compositions with the identity

Bundled analogues of `pullbackFormsFun_id_comp` and
`pullbackFormsFun_comp_id`. Both are rfl since `id ∘ f = f` and
`f ∘ id = f` definitionally.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ f` equals pullback along `f`. -/
theorem pullbackFormsLinearMap_id_comp
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap ((id : Y → Y) ∘ f) η =
      pullbackFormsLinearMap f η := rfl

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ id` equals pullback along `f`. -/
theorem pullbackFormsLinearMap_comp_id
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap (f ∘ (id : X → X)) η =
      pullbackFormsLinearMap f η := rfl

end JacobianChallenge.TraceDegree
