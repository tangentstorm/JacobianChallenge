import Jacobian.TraceDegree.PullbackFormsLinearMapIdEval
import Jacobian.HolomorphicForms.EvalLinearMapVec

/-!
# Vec-slot distributivity for bundled pullback-along-id

Bundled-LinearMap analogue of `PullbackFunIdEvalVec`: with
`(η, x)` fixed, `pullbackFormsLinearMap (id : X → X) η x` is
linear in the tangent vector slot.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` at `v = 0` is zero. -/
theorem pullbackFormsLinearMap_id_apply_zero_vec
    (η : HolomorphicOneForm E X) (x : X) :
    pullbackFormsLinearMap (id : X → X) η x (0 : E) = 0 := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zero_vec x η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over vec addition. -/
theorem pullbackFormsLinearMap_id_apply_add_vec
    (η : HolomorphicOneForm E X) (x : X) (v w : E) :
    pullbackFormsLinearMap (id : X → X) η x (v + w) =
      pullbackFormsLinearMap (id : X → X) η x v +
        pullbackFormsLinearMap (id : X → X) η x w := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_add_vec x v w η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over vec negation. -/
theorem pullbackFormsLinearMap_id_apply_neg_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x (-v) =
      -pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_neg_vec x v η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over ℂ-scalar mult of vec. -/
theorem pullbackFormsLinearMap_id_apply_smul_vec
    (η : HolomorphicOneForm E X) (x : X) (k : ℂ) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x (k • v) =
      k • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_smul_vec x k v η

end JacobianChallenge.TraceDegree
