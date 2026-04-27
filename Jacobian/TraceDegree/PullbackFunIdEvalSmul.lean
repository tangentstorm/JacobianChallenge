import Jacobian.TraceDegree.PullbackFunIdEvalDist
import Jacobian.HolomorphicForms.EvalLinearMapZsmul

/-!
# Smul/nsmul/zsmul distributivity of pullback-along-id

Continues `PullbackFunIdEvalDist` with scalar-multiplication
distributivity, all proven via `evalLinearMap_*_form` /
`(evalLinearMap x v).map_*`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over ℂ-scalar multiplication of forms. -/
theorem pullbackFormsFun_id_smul_apply_vec
    (k : ℂ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (k • η) x v =
      k • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact (evalLinearMap x v).map_smul k η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over `ℕ`-scalar multiplication. -/
theorem pullbackFormsFun_id_nsmul_apply_vec
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (n • η) x v =
      n • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_nsmul x v n η

set_option linter.unusedSectionVars false in
/-- Pullback along `id` distributes over `ℤ`-scalar multiplication. -/
theorem pullbackFormsFun_id_zsmul_apply_vec
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (n • η) x v =
      n • pullbackFormsFun (id : X → X) η x v := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]
  exact evalLinearMap_zsmul x v n η

set_option linter.unusedSectionVars false in
/-- Composition of `_zero_apply_vec` and `_neg_apply_vec`: pullback
along `id` of `-0 = 0`. -/
theorem pullbackFormsFun_id_neg_zero_apply_vec
    (x : X) (v : E) :
    pullbackFormsFun (id : X → X) (-(0 : HolomorphicOneForm E X)) x v = 0 := by
  rw [neg_zero, pullbackFormsFun_id_zero_apply_vec]

end JacobianChallenge.TraceDegree
