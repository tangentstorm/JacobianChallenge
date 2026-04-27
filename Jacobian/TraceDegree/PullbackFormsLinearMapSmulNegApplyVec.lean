import Jacobian.TraceDegree.PullbackFormsLinearMapSmulNeg

/-!
# Vec-applied forms of `PullbackFormsLinearMapSmulNeg`

Pointwise vec-applied versions of the combined smul/neg
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

/-- Vec-applied: `pullback f (k • -η) x v = -(k • pullback f η x v)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_neg_apply_vec
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (k • -η) x v =
      -(k • pullbackFormsLinearMap f η x v) := by
  rw [pullbackFormsLinearMap_smul_neg]; rfl

/-- Vec-applied: `pullback f (-(k • η)) x v = -(k • pullback f η x v)`. -/
@[simp] theorem pullbackFormsLinearMap_neg_smul_apply_vec
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (-(k • η)) x v =
      -(k • pullbackFormsLinearMap f η x v) := by
  rw [pullbackFormsLinearMap_neg_smul]; rfl

/-- Vec-applied: `pullback f (-η + ζ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_neg_add_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (-η + ζ) x v =
      -pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_neg_add]; rfl

/-- Vec-applied: `pullback f (η + -ζ) x v` distributes (subtraction form). -/
@[simp] theorem pullbackFormsLinearMap_add_neg_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η + -ζ) x v =
      pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_add_neg]; rfl

end JacobianChallenge.TraceDegree
