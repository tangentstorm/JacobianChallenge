import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear

/-!
# Right-associated 3-argument bundled-pullback ring identities

Companion to `PullbackFormsLinearMapTriple`: the same shapes but
with the second binary operation grouped on the right
(i.e. `η ± (ζ ± ξ)`), for arbitrary `f`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullback f (η + (ζ + ξ))` distributes (right-associated add). -/
@[simp] theorem pullbackFormsLinearMap_add_add_right
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + (ζ + ξ)) =
      pullbackFormsLinearMap f η +
        (pullbackFormsLinearMap f ζ + pullbackFormsLinearMap f ξ) := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_add]

/-- `pullback f (η + (ζ - ξ))` distributes. -/
@[simp] theorem pullbackFormsLinearMap_add_sub_right
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + (ζ - ξ)) =
      pullbackFormsLinearMap f η +
        (pullbackFormsLinearMap f ζ - pullbackFormsLinearMap f ξ) := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_sub]

/-- `pullback f (η - (ζ + ξ))` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_add_right
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - (ζ + ξ)) =
      pullbackFormsLinearMap f η -
        (pullbackFormsLinearMap f ζ + pullbackFormsLinearMap f ξ) := by
  rw [pullbackFormsLinearMap_sub, pullbackFormsLinearMap_add]

/-- `pullback f (η - (ζ - ξ))` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_sub_right
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - (ζ - ξ)) =
      pullbackFormsLinearMap f η -
        (pullbackFormsLinearMap f ζ - pullbackFormsLinearMap f ξ) := by
  rw [pullbackFormsLinearMap_sub, pullbackFormsLinearMap_sub]

end JacobianChallenge.TraceDegree
