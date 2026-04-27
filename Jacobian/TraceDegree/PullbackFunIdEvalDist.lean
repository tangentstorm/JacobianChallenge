import Jacobian.TraceDegree.PullbackFunIdEval

/-!
# Distributivity of pullback-along-id through `evalLinearMap`

Pullback along `id` distributes over the form-slot operations
(zero/add/neg/sub) at fixed `(x, v)`, with the same shape as
`evalLinearMap`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id` of the zero form is zero (vec-applied). -/
theorem pullbackFormsFun_id_zero_apply_vec (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (0 : HolomorphicOneForm E X) x v = 0 := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_zero

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over form addition. -/
theorem pullbackFormsFun_id_add_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (η + ζ) x v =
      pullbackFormsFun (id : X → X) η x v +
        pullbackFormsFun (id : X → X) ζ x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_add η ζ

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over form negation. -/
theorem pullbackFormsFun_id_neg_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (-η) x v =
      -pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_neg η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over form subtraction. -/
theorem pullbackFormsFun_id_sub_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (η - ζ) x v =
      pullbackFormsFun (id : X → X) η x v -
        pullbackFormsFun (id : X → X) ζ x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_sub η ζ

end JacobianChallenge.TraceDegree
