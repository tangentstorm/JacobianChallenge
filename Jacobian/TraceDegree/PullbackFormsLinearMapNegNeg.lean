import Jacobian.TraceDegree.PullbackFormsLinearMapApply

/-!
# Double-negation collapse for bundled `pullbackFormsLinearMap`

Form-side double-negation collapse identities for the bundled
pullback, at function-level, at-point, and vec-applied levels.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Bundled pullback collapses double-negation at the function level. -/
@[simp] theorem pullbackFormsLinearMap_neg_neg
    (f : X → Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (- -η) = pullbackFormsLinearMap f η := by
  rw [neg_neg]

/-- Bundled pullback collapses double-negation at-point. -/
@[simp] theorem pullbackFormsLinearMap_neg_neg_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f (- -η) x = pullbackFormsLinearMap f η x := by
  rw [neg_neg]

/-- Bundled pullback collapses double-negation vec-applied. -/
@[simp] theorem pullbackFormsLinearMap_neg_neg_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (- -η) x v =
      pullbackFormsLinearMap f η x v := by
  rw [neg_neg]

/-- Bundled pullback of `-(η - ζ)` is `-(pullback (η - ζ))`. -/
@[simp] theorem pullbackFormsLinearMap_neg_sub
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (-(η - ζ)) =
      -pullbackFormsLinearMap f (η - ζ) :=
  map_neg _ _

end JacobianChallenge.TraceDegree
