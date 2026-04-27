import Jacobian.TraceDegree.PullbackFunIdEvalSmul
import Jacobian.HolomorphicForms.EvalLinearMapVec

/-!
# Vec-slot distributivity for pullback-along-id

Vec-side analogue of `PullbackFunIdEvalDist`: with `(η, x)` fixed,
pullback along `id` distributes over addition / negation / scalar
multiplication of the tangent vector.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id` at `v = 0` is zero. -/
theorem pullbackFormsFun_id_apply_zero_vec
    (η : HolomorphicOneForm E X) (x : X) :
    pullbackFormsFun (id : X → X) η x (0 : E) = 0 := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zero_vec x η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over vec addition. -/
theorem pullbackFormsFun_id_apply_add_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsFun (id : X → X) η x (v + w) =
      pullbackFormsFun (id : X → X) η x v +
        pullbackFormsFun (id : X → X) η x w := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_add_vec x v w η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over vec negation. -/
theorem pullbackFormsFun_id_apply_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x (-v) =
      -pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_neg_vec x v η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over ℂ-scalar multiplication of vec. -/
theorem pullbackFormsFun_id_apply_smul_vec
    (η : HolomorphicOneForm E X) (x : X) (k : ℂ) (v : E) :
    pullbackFormsFun (id : X → X) η x (k • v) =
      k • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_smul_vec x k v η

end JacobianChallenge.TraceDegree
