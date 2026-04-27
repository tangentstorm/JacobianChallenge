import Jacobian.TraceDegree.PullbackFormsLinearMap

/-!
# Zero/neg/add identities involving the form `0`

Small ring-rewrite trivialities for the bundled `pullbackFormsLinearMap`
acting on form-side expressions that contain `(0 : HolomorphicOneForm E Y)`.
Useful as direct simp targets so callers don't have to chain
`add_zero`/`zero_add`/`neg_zero` themselves.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Bundled pullback of `η + (-η)` is `0`. -/
@[simp] theorem pullbackFormsLinearMap_add_neg_self
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + -η) = 0 := by
  rw [add_neg_cancel, map_zero]

/-- Bundled pullback of `-0` is `0`. -/
@[simp] theorem pullbackFormsLinearMap_neg_zero
    (f : X → Y) :
    pullbackFormsLinearMap f (-(0 : HolomorphicOneForm E Y)) = 0 := by
  rw [neg_zero, map_zero]

/-- Bundled pullback ignores a right-`0` summand. -/
@[simp] theorem pullbackFormsLinearMap_add_zero
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + 0) = pullbackFormsLinearMap f η := by
  rw [add_zero]

/-- Bundled pullback ignores a left-`0` summand. -/
@[simp] theorem pullbackFormsLinearMap_zero_add
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (0 + η) = pullbackFormsLinearMap f η := by
  rw [zero_add]

end JacobianChallenge.TraceDegree
