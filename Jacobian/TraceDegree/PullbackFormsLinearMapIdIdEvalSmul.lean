import Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEvalVec
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalSmul

/-!
# Bundled along-(id ∘ id): integer-scalar forwarders

Closes the `id ∘ id` forwarder bank with form-slot ℕ/ℤ-smul plus
vec-slot ℕ/ℤ-smul. Each forwards via rfl through to the bundled
along-id result.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over `ℕ`-scalar form mult. -/
theorem pullbackFormsLinearMap_id_id_nsmul_apply_vec
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (n • η) x v =
      n • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_nsmul_apply_vec n η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_id_id_zsmul_apply_vec
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) (n • η) x v =
      n • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_zsmul_apply_vec n η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over `ℕ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_id_apply_nsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℕ) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (n • v) =
      n • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_apply_nsmul_vec η x n v

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id ∘ id` distributes over `ℤ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_id_apply_zsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℤ) (v : E) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x (n • v) =
      n • pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η x v :=
  pullbackFormsLinearMap_id_apply_zsmul_vec η x n v

end JacobianChallenge.TraceDegree
