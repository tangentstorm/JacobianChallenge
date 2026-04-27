import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstVec

/-!
# Vec-slot sub/smul/zero/neg-neg extras for bundled comp-const pullbacks

Continues `PullbackFormsLinearMapCompConstVec` with subtraction,
ℂ-scalar multiplication, the `v = 0` case, and the
double-negation cancel for both bundled comp-const pullbacks.
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
/-- Bundled pullback along `f ∘ const x₀` distributes over vec subtraction. -/
theorem pullbackFormsLinearMap_comp_const_apply_sub_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v w : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x (v - w) =
      pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v -
        pullbackFormsLinearMap (f ∘ Function.const X x₀) η x w := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over ℂ-scalar mult of vec. -/
theorem pullbackFormsLinearMap_comp_const_apply_smul_vec
    (f : Y → Z) (x₀ : Y) (k : ℂ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x (k • v) =
      k • pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over vec subtraction. -/
theorem pullbackFormsLinearMap_const_comp_apply_sub_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v w : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x (v - w) =
      pullbackFormsLinearMap (Function.const Y z ∘ f) η x v -
        pullbackFormsLinearMap (Function.const Y z ∘ f) η x w := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over ℂ-scalar mult of vec. -/
theorem pullbackFormsLinearMap_const_comp_apply_smul_vec
    (z : Z) (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x (k • v) =
      k • pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, smul_zero]

end JacobianChallenge.TraceDegree
