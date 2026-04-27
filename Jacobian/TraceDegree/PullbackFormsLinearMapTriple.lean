import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear

/-!
# Three-argument bundled-pullback ring identities

A handful of distributivity laws involving three forms in a single
add/sub combination, for arbitrary `f`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullback f ((η + ζ) + ξ)` distributes (left-associated add). -/
@[simp] theorem pullbackFormsLinearMap_add_add
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((η + ζ) + ξ) =
      pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ +
        pullbackFormsLinearMap f ξ := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_add]

/-- `pullback f ((η - ζ) + ξ)` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_add
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((η - ζ) + ξ) =
      pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ +
        pullbackFormsLinearMap f ξ := by
  rw [pullbackFormsLinearMap_add, pullbackFormsLinearMap_sub]

/-- `pullback f ((η + ζ) - ξ)` distributes. -/
@[simp] theorem pullbackFormsLinearMap_add_sub
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((η + ζ) - ξ) =
      pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ -
        pullbackFormsLinearMap f ξ := by
  rw [pullbackFormsLinearMap_sub, pullbackFormsLinearMap_add]

/-- `pullback f ((η - ζ) - ξ)` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_sub
    (f : X → Y) (η ζ ξ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f ((η - ζ) - ξ) =
      pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ -
        pullbackFormsLinearMap f ξ := by
  rw [pullbackFormsLinearMap_sub, pullbackFormsLinearMap_sub]

end JacobianChallenge.TraceDegree
