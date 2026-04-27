import Jacobian.TraceDegree.PullbackFunIdEvalVec
import Jacobian.HolomorphicForms.EvalLinearMapVecExtra

/-!
# Sub/nsmul/zsmul vec-slot distributivity for pullback-along-id

Continues `PullbackFunIdEvalVec` with the missing subtraction and
integer-scalar vec cases.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over vec subtraction. -/
theorem pullbackFormsFun_id_apply_sub_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsFun (id : X → X) η x (v - w) =
      pullbackFormsFun (id : X → X) η x v -
        pullbackFormsFun (id : X → X) η x w := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_sub_vec x v w η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over `ℕ`-scalar multiplication of vec. -/
theorem pullbackFormsFun_id_apply_nsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℕ) (v : E) :
    pullbackFormsFun (id : X → X) η x (n • v) =
      n • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_nsmul_vec x n v η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over `ℤ`-scalar multiplication of vec. -/
theorem pullbackFormsFun_id_apply_zsmul_vec
    (η : HolomorphicOneForm E X) (x : X) (n : ℤ) (v : E) :
    pullbackFormsFun (id : X → X) η x (n • v) =
      n • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zsmul_vec x n v η

set_option linter.unusedSectionVars false in
/-- Double-vec-negation cancels under pullback-along-id. -/
theorem pullbackFormsFun_id_apply_neg_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x (- -v) =
      pullbackFormsFun (id : X → X) η x v := by
  rw [neg_neg]

end JacobianChallenge.TraceDegree
