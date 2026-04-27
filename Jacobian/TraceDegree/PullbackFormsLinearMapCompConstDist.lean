import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstApplyVec

/-!
# Trivial form-slot distributivity for bundled comp-const pullbacks

Form-slot distributivity for the bundled pullbacks along
`f ∘ const X x₀` and `const Y z ∘ f`. Both pullbacks vanish, so all
laws reduce to `0 = …`-style identities. Useful as direct simp
targets so callers don't need to re-derive.
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
/-- Bundled pullback along `f ∘ const x₀` distributes over form addition
(both sides are zero). -/
theorem pullbackFormsLinearMap_comp_const_add_apply_vec
    (f : Y → Z) (x₀ : Y) (η ζ : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) (η + ζ) x v =
      pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v +
        pullbackFormsLinearMap (f ∘ Function.const X x₀) ζ x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `f ∘ const x₀` distributes over form negation. -/
theorem pullbackFormsLinearMap_comp_const_neg_apply_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) (-η) x v =
      -pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v := by
  rw [pullbackFormsLinearMap_comp_const_apply_vec,
      pullbackFormsLinearMap_comp_const_apply_vec, neg_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over form addition
(both sides are zero). -/
theorem pullbackFormsLinearMap_const_comp_add_apply_vec
    (z : Z) (f : X → Y) (η ζ : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) (η + ζ) x v =
      pullbackFormsLinearMap (Function.const Y z ∘ f) η x v +
        pullbackFormsLinearMap (Function.const Y z ∘ f) ζ x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, add_zero]

set_option linter.unusedSectionVars false in
/-- Bundled pullback along `const z ∘ f` distributes over form negation. -/
theorem pullbackFormsLinearMap_const_comp_neg_apply_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) (-η) x v =
      -pullbackFormsLinearMap (Function.const Y z ∘ f) η x v := by
  rw [pullbackFormsLinearMap_const_comp_apply_vec,
      pullbackFormsLinearMap_const_comp_apply_vec, neg_zero]

end JacobianChallenge.TraceDegree
