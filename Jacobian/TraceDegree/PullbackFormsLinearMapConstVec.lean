import Jacobian.TraceDegree.PullbackFormsLinearMapConstApplyVec

/-!
# Trivial vec-slot distributivity of bundled pullback along a constant map

Vec-slot analogue of `PullbackFormsLinearMapConstDist`. Since
`pullbackFormsLinearMap (Function.const X y) η x v = 0` for all
`v`, all vec-slot distributivity laws collapse to `0 = …`-style
identities.
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
/-- Bundled pullback along a constant map at `v = 0` is zero. -/
theorem pullbackFormsLinearMap_const_apply_zero_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap (Function.const X y) η x (0 : E) = 0 :=
  pullbackFormsLinearMap_const_apply_vec y η x 0

set_option linter.unusedSectionVars false in
/--
Bundled pullback along a constant map distributes over vec addition
(both sides are zero).
-/
theorem pullbackFormsLinearMap_const_apply_add_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v w : E) :
    pullbackFormsLinearMap (Function.const X y) η x (v + w) =
      pullbackFormsLinearMap (Function.const X y) η x v +
        pullbackFormsLinearMap (Function.const X y) η x w := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over vec negation. -/
theorem pullbackFormsLinearMap_const_apply_neg_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x (-v) =
      -pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, neg_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over ℂ-scalar mult of vec. -/
theorem pullbackFormsLinearMap_const_apply_smul_vec
    (y : Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x (k • v) =
      k • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

end JacobianChallenge.TraceDegree
