import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstIntSmul

/-!
# ℤ-scalar trivial dist for bundled comp-const pullbacks

Closes the integer-scalar picture for both bundled comp-const
pullbacks: `ℤ`-smul on form-slot and on vec-slot, both
`f ∘ const x₀` and `const z ∘ f`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [TopologicalSpace Z] [ChartedSpace E Z]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Z]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_comp_const_zsmul_apply_vec
    (f : Y → Z) (x₀ : Y) (n : ℤ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) (n • η) x v =
      n • pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over `ℤ`-scalar form mult. -/
theorem pullbackFormsLinearMap_const_comp_zsmul_apply_vec
    (z : Z) (f : X → Y) (n : ℤ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) (n • η) x v =
      n • pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over `ℤ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_comp_const_apply_zsmul_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (n : ℤ) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x (n • v) =
      n • pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over `ℤ`-scalar mult of vec. -/
theorem pullbackFormsLinearMap_const_comp_apply_zsmul_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (n : ℤ) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x (n • v) =
      n • pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, smul_zero]

end JacobianChallenge.TraceDegree
