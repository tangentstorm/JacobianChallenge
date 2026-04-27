import Jacobian.TraceDegree.PullbackFunId
import Jacobian.TraceDegree.PullbackFunIdApply
import Jacobian.TraceDegree.PullbackFunIdApplyVec
import Jacobian.TraceDegree.PullbackFormsLinearMapId

/-!
# Pullback along `id ∘ id` collapses to identity pullback

`(id ∘ id : X → X) = id` is rfl, so the pullback agrees with
`pullbackFormsFun_id`. Closes the trivial corner of the
composition matrix where both factors are the identity.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id ∘ id` is the underlying form. -/
@[simp] theorem pullbackFormsFun_id_id
    (η : HolomorphicOneForm E X) :
    pullbackFormsFun ((id : X → X) ∘ (id : X → X)) η = η.toFun :=
  pullbackFormsFun_id η

set_option linter.unusedSectionVars false in
/-- Pointwise apply form. -/
@[simp] theorem pullbackFormsFun_id_id_apply
    (η : HolomorphicOneForm E X) (x : X) :
    pullbackFormsFun ((id : X → X) ∘ (id : X → X)) η x = η.toFun x := by
  rw [pullbackFormsFun_id_id]

set_option linter.unusedSectionVars false in
/-- Vector-apply form. -/
@[simp] theorem pullbackFormsFun_id_id_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun ((id : X → X) ∘ (id : X → X)) η x v = η.toFun x v := by
  rw [pullbackFormsFun_id_id]; rfl

set_option linter.unusedSectionVars false in
/-- Bundled-LinearMap pointwise form. -/
@[simp] theorem pullbackFormsLinearMap_id_id_apply
    (η : HolomorphicOneForm E X) :
    pullbackFormsLinearMap ((id : X → X) ∘ (id : X → X)) η = η.toFun :=
  pullbackFormsFun_id_id η

end JacobianChallenge.TraceDegree
