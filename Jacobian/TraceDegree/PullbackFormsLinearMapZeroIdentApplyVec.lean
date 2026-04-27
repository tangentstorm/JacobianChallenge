import Jacobian.TraceDegree.PullbackFormsLinearMapZeroIdent

/-!
# Vec-applied forms of `PullbackFormsLinearMapZeroIdent`

Pointwise vec-applied forms of the bundled-pullback zero/neg/add
trivialities. Each forwards via the function-level identity plus a
single `rfl`-style application. Useful as direct simp targets at
the vec-applied layer.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vec-applied: `pullbackFormsLinearMap f (η + -η) x v = 0`. -/
@[simp] theorem pullbackFormsLinearMap_add_neg_self_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η + -η) x v = 0 := by
  rw [pullbackFormsLinearMap_add_neg_self]; rfl

/-- Vec-applied: `pullbackFormsLinearMap f (-0) x v = 0`. -/
@[simp] theorem pullbackFormsLinearMap_neg_zero_apply_vec
    (f : X → Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (-(0 : HolomorphicOneForm E Y)) x v = 0 := by
  rw [pullbackFormsLinearMap_neg_zero]; rfl

/-- Vec-applied: `pullbackFormsLinearMap f (η + 0) x v` ignores the right zero. -/
@[simp] theorem pullbackFormsLinearMap_add_zero_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η + 0) x v =
      pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_add_zero]

/-- Vec-applied: `pullbackFormsLinearMap f (0 + η) x v` ignores the left zero. -/
@[simp] theorem pullbackFormsLinearMap_zero_add_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (0 + η) x v =
      pullbackFormsLinearMap f η x v := by
  rw [pullbackFormsLinearMap_zero_add]

end JacobianChallenge.TraceDegree
