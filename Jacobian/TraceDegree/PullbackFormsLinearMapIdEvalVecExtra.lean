import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec
import Jacobian.HolomorphicForms.EvalLinearMapVecExtra

/-!
# Sub/nsmul/zsmul vec-slot distributivity for bundled pullback-along-id

Continues `PullbackFormsLinearMapIdEvalVec` with the missing
subtraction and integer-scalar vec cases at the bundled-LinearMap
layer.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over vec subtraction. -/
theorem pullbackFormsLinearMap_id_apply_sub_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsLinearMap (id : X → X) η x (v - w) =
      pullbackFormsLinearMap (id : X → X) η x v -
        pullbackFormsLinearMap (id : X → X) η x w := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_sub_vec x v w η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over `ℕ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_apply_nsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℕ) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x (n • v) =
      n • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_nsmul_vec x n v η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over `ℤ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_apply_zsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℤ) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x (n • v) =
      n • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zsmul_vec x n v η

set_option linter.unusedSectionVars false in
/-- Double-vec-negation cancels under bundled pullback-along-id. -/
theorem pullbackFormsLinearMap_id_apply_neg_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x (- -v) =
      pullbackFormsLinearMap (id : X → X) η x v := by
  rw [neg_neg]

end JacobianChallenge.TraceDegree
