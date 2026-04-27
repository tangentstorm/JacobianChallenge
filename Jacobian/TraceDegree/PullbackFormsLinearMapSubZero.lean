import Jacobian.TraceDegree.PullbackFormsLinearMapZeroIdent

/-!
# Sub/zero ring-rewrite identities for bundled `pullbackFormsLinearMap`

Continues `PullbackFormsLinearMapZeroIdent` with sub-self,
neg-add-self, and zero-sub / sub-zero variants.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Bundled pullback of `-η + η` is `0`. -/
@[simp] theorem pullbackFormsLinearMap_neg_add_self
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (-η + η) = 0 := by
  rw [neg_add_cancel, map_zero]

/-- Bundled pullback of `η - η` is `0`. -/
@[simp] theorem pullbackFormsLinearMap_sub_self
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - η) = 0 := by
  rw [sub_self, map_zero]

/-- Bundled pullback of `0 - η` negates. -/
@[simp] theorem pullbackFormsLinearMap_zero_sub
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (0 - η) =
      -pullbackFormsLinearMap f η := by
  rw [zero_sub, map_neg]

/-- Bundled pullback of `η - 0` is `pullbackFormsLinearMap f η`. -/
@[simp] theorem pullbackFormsLinearMap_sub_zero
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - 0) = pullbackFormsLinearMap f η := by
  rw [sub_zero]

end JacobianChallenge.TraceDegree
