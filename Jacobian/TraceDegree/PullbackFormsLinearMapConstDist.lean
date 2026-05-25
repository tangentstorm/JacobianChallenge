import Jacobian.TraceDegree.PullbackFormsLinearMapConstApplyVec

/-!
# Trivial distributivity of bundled pullback along a constant map

Since `pullbackFormsLinearMap (Function.const X y) η x v = 0` for
all `η, x, v`, all distributivity laws over the form slot reduce to
`0 = 0`-style identities. We package them so downstream rewrites
have direct lemmas to fire on (rather than re-deriving via the
const collapse each time).
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/--
Bundled pullback along a constant map distributes over form addition
(both sides are zero).
-/
theorem pullbackFormsLinearMap_const_add_apply_vec
    (y : Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (η + ζ) x v =
      pullbackFormsLinearMap (Function.const X y) η x v +
        pullbackFormsLinearMap (Function.const X y) ζ x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over form negation. -/
theorem pullbackFormsLinearMap_const_neg_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (-η) x v =
      -pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, neg_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over form subtraction. -/
theorem pullbackFormsLinearMap_const_sub_apply_vec
    (y : Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (η - ζ) x v =
      pullbackFormsLinearMap (Function.const X y) η x v -
        pullbackFormsLinearMap (Function.const X y) ζ x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over ℂ-scalar form mult. -/
theorem pullbackFormsLinearMap_const_smul_apply_vec
    (y : Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) (k • η) x v =
      k • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

end JacobianChallenge.TraceDegree
