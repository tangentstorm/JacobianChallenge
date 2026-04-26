import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunSub

/-!
# Pointwise apply forms for `pullbackFormsFun_{add,sub}`

The function-level simp lemmas `pullbackFormsFun_add` and
`pullbackFormsFun_sub` plus `Pi.add_apply` / `Pi.sub_apply` already
let `simp` derive the pointwise versions, but explicit apply-forms
are useful for direct `rw`/`exact` proofs.

Out of scope of the in-flight Aristotle job `82687eb7`
(`PullbackFunSimpApply.lean`), which targets only
`pullbackFormsFun_{zero,neg,smul}_apply`. This file lives in a
separate module so it does not conflict.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Pointwise apply form: pullback distributes over addition. -/
@[simp] theorem pullbackFormsFun_add_apply
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f (η + ζ) x =
      pullbackFormsFun f η x + pullbackFormsFun f ζ x := by
  rw [pullbackFormsFun_add]; rfl

/-- Pointwise apply form: pullback distributes over subtraction. -/
@[simp] theorem pullbackFormsFun_sub_apply
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f (η - ζ) x =
      pullbackFormsFun f η x - pullbackFormsFun f ζ x := by
  rw [pullbackFormsFun_sub]; rfl

end JacobianChallenge.TraceDegree
