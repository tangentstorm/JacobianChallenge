import Jacobian.TraceDegree.PullbackFormsLinearMapCompConst
import Jacobian.TraceDegree.PullbackFunCompConstApply

/-!
# Bundled-LinearMap vec-apply forms of comp-const lemmas

Vector-application forms of `pullbackFormsLinearMap_comp_const_apply`
and `pullbackFormsLinearMap_const_comp_apply`. All trivially zero.
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
/-- Vec-apply form: bundled pullback along `f ∘ const x₀` evaluated on a
tangent vector is zero. -/
@[simp] theorem pullbackFormsLinearMap_comp_const_apply_vec
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η x v = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form: bundled pullback along `const z ∘ f` evaluated on a
tangent vector is zero. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_apply_vec
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η x v = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp]; rfl

set_option linter.unusedSectionVars false in
/-- Function-level form: bundled pullback along `f ∘ const x₀` is the
zero function in `X → E →L[ℂ] ℂ`. -/
theorem pullbackFormsLinearMap_comp_const
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsLinearMap (f ∘ Function.const X x₀) η = 0 := by
  rw [pullbackFormsLinearMap_apply]; exact pullbackFormsFun_comp_const f x₀ η

set_option linter.unusedSectionVars false in
/-- Function-level form: bundled pullback along `const z ∘ f` is the
zero function in `X → E →L[ℂ] ℂ`. -/
theorem pullbackFormsLinearMap_const_comp
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsLinearMap (Function.const Y z ∘ f) η = 0 := by
  rw [pullbackFormsLinearMap_apply]; exact pullbackFormsFun_const_comp z f η

end JacobianChallenge.TraceDegree
