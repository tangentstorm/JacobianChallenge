import Jacobian.TraceDegree.PullbackFunCompConst
import Jacobian.TraceDegree.PullbackFunConstComp
import Jacobian.TraceDegree.PullbackFormsLinearMapApply

/-!
# Pullback along a composition of two constant maps

`Function.const Y z ∘ Function.const X y = Function.const X z` rfl.
Pullback along it is therefore zero (`pullbackFormsFun_const`).

This is a small corollary — a clean simp form that downstream
`simp` chains can land on without first un-composing.
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
/-- Pullback along a constant-of-constant composition is zero. -/
@[simp] theorem pullbackFormsFun_const_comp_const
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsFun (Function.const Y z ∘ Function.const X y) η = 0 :=
  pullbackFormsFun_const_comp z (Function.const X y) η

set_option linter.unusedSectionVars false in
/-- Pointwise apply form. -/
@[simp] theorem pullbackFormsFun_const_comp_const_apply
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsFun (Function.const Y z ∘ Function.const X y) η x = 0 := by
  rw [pullbackFormsFun_const_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form. -/
@[simp] theorem pullbackFormsFun_const_comp_const_apply_vec
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsFun (Function.const Y z ∘ Function.const X y) η x v = 0 := by
  rw [pullbackFormsFun_const_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap pointwise apply form. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_const_apply
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsLinearMap (Function.const Y z ∘ Function.const X y) η x = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp_const]; rfl

end JacobianChallenge.TraceDegree
