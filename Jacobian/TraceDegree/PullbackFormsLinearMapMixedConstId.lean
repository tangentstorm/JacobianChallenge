import Jacobian.TraceDegree.PullbackFunMixedConstIdApply
import Jacobian.TraceDegree.PullbackFormsLinearMapApply

/-!
# Bundled-LinearMap mixed `id ∘ const` and `const ∘ id`

Bundled-LinearMap apply forms of `pullbackFormsFun_id_comp_const`
and `pullbackFormsFun_const_comp_id`. All trivially zero.
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
/-- Bundled-LinearMap apply form: pullback along `id ∘ const X y`. -/
@[simp] theorem pullbackFormsLinearMap_id_comp_const_apply
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap ((id : Y → Y) ∘ Function.const X y) η x = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_id_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap vec-apply form: pullback along `id ∘ const X y`. -/
@[simp] theorem pullbackFormsLinearMap_id_comp_const_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap ((id : Y → Y) ∘ Function.const X y) η x v = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_id_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap apply form: pullback along `const X y ∘ id`. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_id_apply
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap (Function.const X y ∘ (id : X → X)) η x = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp_id]; rfl

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap vec-apply form: pullback along `const X y ∘ id`. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_id_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y ∘ (id : X → X)) η x v = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp_id]; rfl

end JacobianChallenge.TraceDegree
