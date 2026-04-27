import Jacobian.TraceDegree.PullbackFormsLinearMapIdEval

/-!
# Form-slot distributivity for bundled pullback-along-id

Bundled-LinearMap analogue of `PullbackFunIdEvalDist`: at fixed
`(x, v)`, pullback along `id` distributes over the form-slot
operations zero/neg/sub, plus an integer-scalar variant.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` of the zero form is zero (vec-applied). -/
theorem pullbackFormsLinearMap_id_zero_apply_vec (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (0 : HolomorphicOneForm E X) x v = 0 := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_zero

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over form negation (vec form). -/
theorem pullbackFormsLinearMap_id_neg_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (-η) x v =
      -pullbackFormsLinearMap (id : X → X) η x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_neg η

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `id` distributes over form subtraction (vec form). -/
theorem pullbackFormsLinearMap_id_sub_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (η - ζ) x v =
      pullbackFormsLinearMap (id : X → X) η x v -
        pullbackFormsLinearMap (id : X → X) ζ x v := by
  rw [pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap,
      pullbackFormsLinearMap_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_sub η ζ

set_option linter.unusedSectionVars false in
/-- Double-form-negation cancels under bundled pullback-along-id. -/
theorem pullbackFormsLinearMap_id_neg_neg_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) (- -η) x v =
      pullbackFormsLinearMap (id : X → X) η x v := by
  rw [neg_neg]

end JacobianChallenge.TraceDegree
