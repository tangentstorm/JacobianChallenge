import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstApplyVec

/-!
# Trivial vec-slot dist for bundled comp-const pullbacks

Vec-slot mirror of `PullbackFormsLinearMapCompConstDist`. Both
bundled comp-const pullbacks vanish, so each vec-slot
distributivity law reduces to a `0 = …`-style identity.
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
/-- Bundled pullback along `f ∘ const x₀` distributes over vec addition. -/
theorem pullbackFormsLinearMap_comp_const_apply_add_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v w : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x (v + w) =
      pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v +
        pullbackFormsLinearMap (f ∘ Function.const X x₀) η x w := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over vec negation. -/
theorem pullbackFormsLinearMap_comp_const_apply_neg_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x (-v) =
      -pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, neg_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over vec addition. -/
theorem pullbackFormsLinearMap_const_comp_apply_add_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v w : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x (v + w) =
      pullbackFormsLinearMap (Function.const Y z ∘ f) η x v +
        pullbackFormsLinearMap (Function.const Y z ∘ f) η x w := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over vec negation. -/
theorem pullbackFormsLinearMap_const_comp_apply_neg_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x (-v) =
      -pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, neg_zero]

end JacobianChallenge.TraceDegree
