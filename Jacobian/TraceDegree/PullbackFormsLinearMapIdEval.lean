import Jacobian.TraceDegree.PullbackFunIdEval
import Jacobian.TraceDegree.PullbackFormsLinearMapId
import Jacobian.TraceDegree.PullbackFormsLinearMapApply

/-!
# Bundled-LinearMap pullback-along-id ↔ `evalLinearMap`

Bundled-level analogue of `PullbackFunIdEval`. Reduces
`pullbackFormsLinearMap (id : X → X) η x v` to
`evalLinearMap x v η` via the existing
`pullbackFormsLinearMap_apply_at` rfl bridge.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback-along-id at `(x, v)` equals `evalLinearMap x v η`. -/
theorem pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x v = evalLinearMap x v η := by
  rw [pullbackFormsLinearMap_apply_at]
  exact pullbackFormsFun_id_apply_vec_eq_evalLinearMap η x v

set_option linter.unusedSectionVars false in
/-- Bundled pullback-along-id is zero at `(x, v)` iff `evalLinearMap` is. -/
theorem pullbackFormsLinearMap_id_eq_zero_iff_evalLinearMap_eq_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x v = 0 ↔
      evalLinearMap (E := E) (X := X) x v η = 0 := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over form addition (vec form). -/
theorem pullbackFormsLinearMap_id_add_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (η + ζ) x v =
      pullbackFormsLinearMap (id : X → X) η x v +
        pullbackFormsLinearMap (id : X → X) ζ x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_add η ζ

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over ℂ-scalar form mult. -/
theorem pullbackFormsLinearMap_id_smul_apply_vec
    (k : ℂ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (k • η) x v =
      k • pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_smul k η

end JacobianChallenge.TraceDegree
