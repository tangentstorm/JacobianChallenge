import Jacobian.TraceDegree.PullbackFunConstCompConst

/-!
# Bundled-LinearMap and vec-apply forms of const-of-const composition

Companion file to `PullbackFunConstCompConst`. Adds the bundled
function-level form (whole `X → E →L[ℂ] ℂ` is zero) and the bundled
tangent-vec-apply form. Both trivially zero.
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
/-- Bundled-LinearMap function-level form: pullback along
`Function.const Y z ∘ Function.const X y` is the zero function. -/
theorem pullbackFormsLinearMap_const_comp_const
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsLinearMap (Function.const Y z ∘ Function.const X y) η = 0 := by
  rw [pullbackFormsLinearMap_apply]; exact pullbackFormsFun_const_comp_const z y η

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap vec-apply form. -/
@[simp] theorem pullbackFormsLinearMap_const_comp_const_apply_vec
    (z : Z) (y : Y) (η : HolomorphicOneForm E Z) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const Y z ∘ Function.const X y) η x v = 0 := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_const_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Pullback of `id ∘ Function.const X y` is zero (definitional
collapse of `id ∘ const = const`, then `pullbackFormsFun_const`). -/
@[simp] theorem pullbackFormsFun_id_comp_const
    (y : Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun ((id : Y → Y) ∘ Function.const X y) η = 0 :=
  pullbackFormsFun_const y η

set_option linter.unusedSectionVars false in
/-- Pullback of `Function.const X y ∘ id` is zero. -/
@[simp] theorem pullbackFormsFun_const_comp_id
    (y : Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun (Function.const X y ∘ (id : X → X)) η = 0 :=
  pullbackFormsFun_const y η

end JacobianChallenge.TraceDegree
