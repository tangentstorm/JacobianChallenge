import Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEvalDist
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVecExtra

/-!
# Bundled along-(id ∘ id): vec-slot dist forwarders

Vec-slot forwarders for the bundled pullback along `id ∘ id`,
mirroring `PullbackFormsLinearMapIdEvalVec`/`VecExtra`. Each
forwards via rfl through to the bundled along-id result.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over vec negation. -/
theorem pullbackFormsLinearMap_id_id_apply_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (-v) =
      -pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_apply_neg_vec η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over vec subtraction. -/
theorem pullbackFormsLinearMap_id_id_apply_sub_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (v - w) =
      pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v -
        pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x w :=
  pullbackFormsLinearMap_id_apply_sub_vec η x v w

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over ℂ-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_id_apply_smul_vec
    (η : HolomorphicOneForm E X) (x : X) (k : ℂ) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (k • v) =
      k • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_apply_smul_vec η x k v

set_option linter.unusedSectionVars false in
/-- Double-vec-negation cancels under bundled pullback along `id ∘ id`. -/
theorem pullbackFormsLinearMap_id_id_apply_neg_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (- -v) =
      pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_apply_neg_neg_vec η x v

end JacobianChallenge.TraceDegree
