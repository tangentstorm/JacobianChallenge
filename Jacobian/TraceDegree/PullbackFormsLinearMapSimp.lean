import Jacobian.TraceDegree.PullbackFormsLinearMap

/-!
# Simp lemmas for `pullbackFormsLinearMap`

Named `@[simp]` lemmas exposing the `LinearMap`-derived linearity of
`pullbackFormsLinearMap` (zero, neg, add).  These are auto-derivable
from the `LinearMap` structure but useful as named simp rewrites
alongside the existing `pullbackFormsFun_zero/_neg/_add`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullbackFormsLinearMap` of the zero form is zero. -/
@[simp] theorem pullbackFormsLinearMap_zero
    (f : X → Y) :
    pullbackFormsLinearMap f (0 : HolomorphicOneForm E Y) = 0 := by
  exact LinearMap.map_zero (pullbackFormsLinearMap f)

/-- `pullbackFormsLinearMap` distributes over negation. -/
@[simp] theorem pullbackFormsLinearMap_neg
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (-η) = -pullbackFormsLinearMap f η := by
  exact LinearMap.map_neg (pullbackFormsLinearMap f) η

/-- `pullbackFormsLinearMap` distributes over addition. -/
@[simp] theorem pullbackFormsLinearMap_add
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η + ζ) =
      pullbackFormsLinearMap f η + pullbackFormsLinearMap f ζ := by
  exact LinearMap.map_add (pullbackFormsLinearMap f) η ζ

/-- `pullbackFormsLinearMap` distributes over subtraction. -/
@[simp] theorem pullbackFormsLinearMap_sub
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (η - ζ) =
      pullbackFormsLinearMap f η - pullbackFormsLinearMap f ζ := by
  exact LinearMap.map_sub (pullbackFormsLinearMap f) η ζ

end JacobianChallenge.TraceDegree
