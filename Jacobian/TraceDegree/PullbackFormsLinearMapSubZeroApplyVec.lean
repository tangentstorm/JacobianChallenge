import Jacobian.TraceDegree.PullbackFormsLinearMapSubZero

/-!
# Vec-applied forms of `PullbackFormsLinearMapSubZero`

Pointwise vec-applied forms of the bundled-pullback sub/zero
ring-rewrite identities. Each forwards via the function-level
identity plus a single `rfl`-style application.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vec-applied: `pullbackFormsLinearMap f (-η + η) x v = 0`. -/
@[simp] theorem pullbackFormsLinearMap_neg_add_self_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (-η + η) x v = 0 := by
  rw [pullbackFormsLinearMap_neg_add_self]; rfl

/-- Vec-applied: `pullbackFormsLinearMap f (η - η) x v = 0`. -/
@[simp] theorem pullbackFormsLinearMap_sub_self_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η - η) x v = 0 := by
  rw [pullbackFormsLinearMap_sub_self]; rfl

/-- Vec-applied: `pullbackFormsLinearMap f (0 - η) x v = -pullback ... x v`. -/
@[simp] theorem pullbackFormsLinearMap_zero_sub_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (0 - η) x v =
      -pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_zero_sub]; rfl

/-- Vec-applied: `pullbackFormsLinearMap f (η - 0) x v = pullback η x v`. -/
@[simp] theorem pullbackFormsLinearMap_sub_zero_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η - 0) x v =
      pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_sub_zero]

end JacobianChallenge.TraceDegree
