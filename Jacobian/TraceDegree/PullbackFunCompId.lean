import Jacobian.TraceDegree.PullbackFun

/-!
# Pullback along compositions with the identity

Both `id ∘ f` and `f ∘ id` reduce definitionally to `f`, so the
pullback along these compositions equals the pullback along `f`
itself (rfl).
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/-- Pullback along `id ∘ f` equals pullback along `f`. -/
@[simp] theorem pullbackFormsFun_id_comp
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun ((id : Y → Y) ∘ f) η = pullbackFormsFun f η := rfl

set_option linter.unusedSectionVars false in
/-- Pullback along `f ∘ id` equals pullback along `f`. -/
@[simp] theorem pullbackFormsFun_comp_id
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun (f ∘ (id : X → X)) η = pullbackFormsFun f η := rfl

end JacobianChallenge.TraceDegree
