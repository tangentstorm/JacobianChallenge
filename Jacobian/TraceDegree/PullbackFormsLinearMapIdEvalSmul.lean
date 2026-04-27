import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalDist
import Jacobian.HolomorphicForms.EvalLinearMapZsmul

/-!
# Integer-scalar form-slot distributivity for bundled pullback-along-id

Bundled-LinearMap analogue of `PullbackFunIdEvalSmul`. Adds the
`ℕ`/`ℤ`-scalar form-slot variants and a small `neg-zero` helper.
The `ℂ`-scalar case is already in `PullbackFormsLinearMapIdEval`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over `ℕ`-scalar form mult. -/
theorem pullbackFormsLinearMap_id_nsmul_apply_vec
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (n • η) x v =
      n • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_nsmul x v n η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_id_zsmul_apply_vec
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (n • η) x v =
      n • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zsmul x v n η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` of `-0` (form slot) is zero. -/
theorem pullbackFormsLinearMap_id_neg_zero_apply_vec
    (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (-(0 : HolomorphicOneForm E X)) x v = 0 := by
  rw [neg_zero, pullbackFormsLinearMap_id_zero_apply_vec]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` of `0 - 0` (form slot) is zero. -/
theorem pullbackFormsLinearMap_id_zero_sub_zero_apply_vec
    (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X)
        ((0 : HolomorphicOneForm E X) - (0 : HolomorphicOneForm E X)) x v = 0 := by
  rw [sub_zero, pullbackFormsLinearMap_id_zero_apply_vec]

end JacobianChallenge.TraceDegree
