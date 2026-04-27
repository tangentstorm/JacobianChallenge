import Jacobian.TraceDegree.PullbackFunConstCompConstBundled

/-!
# Apply / vec-apply forms of mixed `id ∘ const` and `const ∘ id`

Pointwise apply and vec-apply forms of last tick's
`pullbackFormsFun_id_comp_const` and `pullbackFormsFun_const_comp_id`.
All trivially zero, since the function-level statements already are.
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
/-- Pointwise apply form of `pullbackFormsFun_id_comp_const`. -/
@[simp] theorem pullbackFormsFun_id_comp_const_apply
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun ((id : Y → Y) ∘ Function.const X y) η x = 0 := by
  rw [pullbackFormsFun_id_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form of `pullbackFormsFun_id_comp_const`. -/
@[simp] theorem pullbackFormsFun_id_comp_const_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun ((id : Y → Y) ∘ Function.const X y) η x v = 0 := by
  rw [pullbackFormsFun_id_comp_const]; rfl

set_option linter.unusedSectionVars false in
/-- Pointwise apply form of `pullbackFormsFun_const_comp_id`. -/
@[simp] theorem pullbackFormsFun_const_comp_id_apply
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun (Function.const X y ∘ (id : X → X)) η x = 0 := by
  rw [pullbackFormsFun_const_comp_id]; rfl

set_option linter.unusedSectionVars false in
/-- Vec-apply form of `pullbackFormsFun_const_comp_id`. -/
@[simp] theorem pullbackFormsFun_const_comp_id_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun (Function.const X y ∘ (id : X → X)) η x v = 0 := by
  rw [pullbackFormsFun_const_comp_id]; rfl

end JacobianChallenge.TraceDegree
