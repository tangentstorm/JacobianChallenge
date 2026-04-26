import Jacobian.TraceDegree.PullbackFun

/-!
# Subtraction linearity of `pullbackFormsFun`

Derives `pullbackFormsFun f (η - ζ) = pullbackFormsFun f η - pullbackFormsFun f ζ`
from the existing `_add` and `_neg` lemmas by rewriting subtraction as
`a + (-b)`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- The pullback distributes over subtraction. -/
@[simp] theorem pullbackFormsFun_sub
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsFun f (η - ζ) = pullbackFormsFun f η - pullbackFormsFun f ζ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, pullbackFormsFun_add, pullbackFormsFun_neg]

end JacobianChallenge.TraceDegree
