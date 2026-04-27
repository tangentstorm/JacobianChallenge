import Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEval
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalSmul
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec

/-!
# Bundled along-(id ∘ id): form/vec-slot dist forwarders

Continues `PullbackFormsLinearMapIdIdEval` with form-slot
neg/sub/smul forwarders and a vec-slot add forwarder. Each lemma
forwards directly to the corresponding bundled along-id result via
the rfl `id ∘ id = id` collapse.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over form negation. -/
theorem pullbackFormsLinearMap_id_id_neg_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (-η) x v =
      -pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_neg_apply_vec η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over form subtraction. -/
theorem pullbackFormsLinearMap_id_id_sub_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (η - ζ) x v =
      pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v -
        pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) ζ x v :=
  pullbackFormsLinearMap_id_sub_apply_vec η ζ x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over ℂ-scalar form mult. -/
theorem pullbackFormsLinearMap_id_id_smul_apply_vec
    (k : ℂ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (k • η) x v =
      k • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_smul_apply_vec k η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over vec addition. -/
theorem pullbackFormsLinearMap_id_id_apply_add_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (v + w) =
      pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v +
        pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x w :=
  pullbackFormsLinearMap_id_apply_add_vec η x v w

end JacobianChallenge.TraceDegree
