import Jacobian.TraceDegree.PullbackFormsLinearMapSmulAdd

/-!
# Vec-applied forms of `PullbackFormsLinearMapSmulAdd`

Pointwise vec-applied versions of the bundled-pullback combined
smul/add/sub identities. Each forwards via the function-level
identity plus a single `rfl`-style application.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vec-applied: `pullback f (k • (η + ζ)) x v = k • (pull η x v + pull ζ x v)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_add_apply_vec
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (k • (η + ζ)) x v =
      k • (pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_smul_add]; rfl

/-- Vec-applied: `pullback f (k • (η - ζ)) x v = k • (pull η x v - pull ζ x v)`. -/
@[simp] theorem pullbackFormsLinearMap_smul_sub_apply_vec
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (k • (η - ζ)) x v =
      k • (pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_smul_sub]; rfl

/-- Vec-applied: `pullback f ((k • η) + ζ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_smul_left_add_apply_vec
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f ((k • η) + ζ) x v =
      k • pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_smul_left_add]; rfl

/-- Vec-applied: `pullback f (η - k • ζ) x v` distributes. -/
@[simp] theorem pullbackFormsLinearMap_sub_smul_right_apply_vec
    (f : X → Y) (k : ℂ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η - k • ζ) x v =
      pullbackFormsLinearMap f η x v -
        k • pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_sub_smul_right]; rfl

end JacobianChallenge.TraceDegree
