import Jacobian.TraceDegree.PullbackFormsLinearMapCompId
import Jacobian.TraceDegree.PullbackFunCompId

/-!
# Bundled-LinearMap pointwise apply forms of comp-id lemmas

Pointwise apply and vec-apply forms of `pullbackFormsLinearMap_id_comp`
and `pullbackFormsLinearMap_comp_id`. All trivially `rfl`, since
`id ∘ f = f` and `f ∘ id = f` definitionally.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/-- Pointwise apply form: bundled pullback along `id ∘ f` at a point. -/
@[simp] theorem pullbackFormsLinearMap_id_comp_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap ((id : Y → Y) ∘ f) η x =
      pullbackFormsLinearMap f η x := rfl

set_option linter.unusedSectionVars false in
/-- Pointwise apply form: bundled pullback along `f ∘ id` at a point. -/
@[simp] theorem pullbackFormsLinearMap_comp_id_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap (f ∘ (id : X → X)) η x =
      pullbackFormsLinearMap f η x := rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form: bundled pullback along `id ∘ f` evaluated on a
tangent vector. -/
@[simp] theorem pullbackFormsLinearMap_id_comp_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : Y → Y) ∘ f) η x v =
      pullbackFormsLinearMap f η x v := rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form: bundled pullback along `f ∘ id` evaluated on a
tangent vector. -/
@[simp] theorem pullbackFormsLinearMap_comp_id_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ (id : X → X)) η x v =
      pullbackFormsLinearMap f η x v := rfl

end JacobianChallenge.TraceDegree
