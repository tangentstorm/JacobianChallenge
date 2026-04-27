import Jacobian.TraceDegree.PullbackFormsLinearMapIdEval
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalDist
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec
import Jacobian.TraceDegree.PullbackFunIdComposeId

/-!
# Bundled-LinearMap pullback along `id ∘ id` ↔ `evalLinearMap`

Since `((id : X → X) ∘ id) = id` definitionally, the bundled
pullback along `id ∘ id` agrees with the bundled pullback along
`id`, and inherits the `evalLinearMap` bridge plus form/vec-slot
linearity laws.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` equals `evalLinearMap x v η`. -/
theorem pullbackFormsLinearMap_id_id_apply_vec_eq_evalLinearMap
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v =
      evalLinearMap x v η :=
  pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` of the zero form is zero (vec-applied). -/
theorem pullbackFormsLinearMap_id_id_zero_apply_vec (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X))
        (0 : HolomorphicOneForm E X) x v = 0 :=
  pullbackFormsLinearMap_id_zero_apply_vec x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over form addition (vec form). -/
theorem pullbackFormsLinearMap_id_id_add_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (η + ζ) x v =
      pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v +
        pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) ζ x v :=
  pullbackFormsLinearMap_id_add_apply_vec η ζ x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` at `v = 0` is zero. -/
theorem pullbackFormsLinearMap_id_id_apply_zero_vec
    (η : HolomorphicOneForm E X) (x : X) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (0 : E) = 0 :=
  pullbackFormsLinearMap_id_apply_zero_vec η x

end JacobianChallenge.TraceDegree
