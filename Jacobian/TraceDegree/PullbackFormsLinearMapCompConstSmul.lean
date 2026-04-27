import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstDist

/-!
# Form-slot smul/sub trivial dist for bundled comp-const pullbacks

Continues `PullbackFormsLinearMapCompConstDist` with form-slot
subtraction and ℂ-scalar multiplication, both for `f ∘ const x₀`
and `const z ∘ f`. Each collapses via the const-pullback zero
identity.
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
/-- Bundled pullback along `f ∘ const x₀` distributes over form subtraction. -/
theorem pullbackFormsLinearMap_comp_const_sub_apply_vec
    (f : Y → Z) (x₀ : Y) (η ζ : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) (η - ζ) x v =
      pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v -
        pullbackFormsLinearMap (f ∘ Function.const X x₀) ζ x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over ℂ-scalar form mult. -/
theorem pullbackFormsLinearMap_comp_const_smul_apply_vec
    (f : Y → Z) (x₀ : Y) (k : ℂ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) (k • η) x v =
      k • pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, smul_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over form subtraction. -/
theorem pullbackFormsLinearMap_const_comp_sub_apply_vec
    (z : Z) (f : X → Y) (η ζ : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) (η - ζ) x v =
      pullbackFormsLinearMap (Function.const Y z ∘ f) η x v -
        pullbackFormsLinearMap (Function.const Y z ∘ f) ζ x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, sub_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over ℂ-scalar form mult. -/
theorem pullbackFormsLinearMap_const_comp_smul_apply_vec
    (z : Z) (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) (k • η) x v =
      k • pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, smul_zero]

end JacobianChallenge.TraceDegree
