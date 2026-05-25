import Jacobian.TraceDegree.PullbackFunCompConst
import Jacobian.TraceDegree.PullbackFunConstComp

/-!
# Pointwise apply / vec-apply forms of comp-const lemmas

Apply and vector-apply forms of `pullbackFormsFun_comp_const` and
`pullbackFormsFun_const_comp`. All trivially zero, since the
function-level results are already zero.
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
/--
Vec-apply form: pullback along `f ∘ const x₀` evaluated on a
tangent vector is zero.
-/
@[simp] theorem pullbackFormsFun_comp_const_apply_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsFun (f ∘ Function.const X x₀) η x v = 0 := by
  rw [pullbackFormsFun_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Pointwise apply form: pullback along `const z ∘ f` is zero. -/
@[simp] theorem pullbackFormsFun_const_comp_apply
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsFun (Function.const Y z ∘ f) η x = 0 := by
  rw [pullbackFormsFun_const_comp]; rfl

set_option linter.unusedSectionVars false in
/--
Vec-apply form: pullback along `const z ∘ f` evaluated on a
tangent vector is zero.
-/
@[simp] theorem pullbackFormsFun_const_comp_apply_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsFun (Function.const Y z ∘ f) η x v = 0 := by
  rw [pullbackFormsFun_const_comp]; rfl

set_option linter.unusedSectionVars false in
/-- Pointwise apply form: pullback along `f ∘ const x₀` is zero. -/
@[simp] theorem pullbackFormsFun_comp_const_apply
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) :
    pullbackFormsFun (f ∘ Function.const X x₀) η x = 0 := by
  rw [pullbackFormsFun_comp_const]; rfl

end JacobianChallenge.TraceDegree
