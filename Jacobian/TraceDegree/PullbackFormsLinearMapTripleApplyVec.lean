import Jacobian.TraceDegree.PullbackFormsLinearMapTriple

/-!
# Vec-applied forms of `PullbackFormsLinearMapTriple`

Pointwise vec-applied versions of the bundled-pullback 3-arg
add/sub combinations. Each forwards via the function-level
identity plus a single `rfl`-style application.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vec-applied: `pullback f ((η + ζ) + ξ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_add_add_apply_vec
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f ((η + ζ) + ξ) x v =
      pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v +
        pullbackFormsLinearMap f ξ x v := by
  rw [pullbackFormsLinearMap_add_add]; rfl

/-- Vec-applied: `pullback f ((η - ζ) + ξ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_add_apply_vec
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f ((η - ζ) + ξ) x v =
      pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v +
        pullbackFormsLinearMap f ξ x v := by
  rw [pullbackFormsLinearMap_sub_add]; rfl

/-- Vec-applied: `pullback f ((η + ζ) - ξ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_add_sub_apply_vec
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f ((η + ζ) - ξ) x v =
      pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v -
        pullbackFormsLinearMap f ξ x v := by
  rw [pullbackFormsLinearMap_add_sub]; rfl

/-- Vec-applied: `pullback f ((η - ζ) - ξ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_sub_apply_vec
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f ((η - ζ) - ξ) x v =
      pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v -
        pullbackFormsLinearMap f ξ x v := by
  rw [pullbackFormsLinearMap_sub_sub]; rfl

end JacobianChallenge.TraceDegree
