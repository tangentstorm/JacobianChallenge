import Jacobian.TraceDegree.PullbackFormsLinearMapApply
import Jacobian.TraceDegree.PullbackFunCompConst
import Jacobian.TraceDegree.PullbackFunConstComp

/-!
# Bundled-LinearMap-level const-composition lemmas

Pointwise lifts of `pullbackFormsFun_comp_const` and
`pullbackFormsFun_const_comp` to the bundled
`pullbackFormsLinearMap`. Both are zero, since pullback along any
constant-factoring map vanishes.
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
/-- Pointwise apply form: bundled pullback along `f ∘ const x₀` is zero. -/
@[simp] theorem pullbackFormsLinearMap_comp_const_apply
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_comp_const]
  rfl

set_option linter.unusedSectionVars false in
/-- Pointwise apply form: bundled pullback along `const z ∘ f` is zero. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_apply
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp]
  rfl

end JacobianChallenge.TraceDegree
