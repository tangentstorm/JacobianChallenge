import Jacobian.TraceDegree.PullbackFormsLinearMapConstVec

/-!
# Sub/nsmul/zsmul vec-slot extras for bundled pullback along a constant map

Continues `PullbackFormsLinearMapConstVec` with the missing
subtraction and integer-scalar vec cases. All of these reduce
trivially via the const-pullback zero collapse.
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
/-- Bundled pullback along a constant map distributes over vec subtraction. -/
theorem pullbackFormsLinearMap_const_apply_sub_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v w : E) :
    pullbackFormsLinearMap (Function.const X y) η x (v - w) =
      pullbackFormsLinearMap (Function.const X y) η x v -
        pullbackFormsLinearMap (Function.const X y) η x w := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over `ℕ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_const_apply_nsmul_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (n : ℕ) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x (n • v) =
      n • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along a constant map distributes over `ℤ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_const_apply_zsmul_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (n : ℤ) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x (n • v) =
      n • pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [pullbackFormsLinearMap_const_apply_vec,
      pullbackFormsLinearMap_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Double-vec-negation cancels under bundled pullback along a constant map. -/
theorem pullbackFormsLinearMap_const_apply_neg_neg_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x (- -v) =
      pullbackFormsLinearMap (Function.const X y) η x v := by
  rw [neg_neg]

end JacobianChallenge.TraceDegree
