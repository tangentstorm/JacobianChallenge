import Jacobian.TraceDegree.PullbackFormsLinearMapIntSmulAdd

/-!
# Vec-applied forms of `PullbackFormsLinearMapIntSmulAdd`

Pointwise vec-applied versions of the bundled-pullback ℕ/ℤ-smul ×
add/sub combined identities. Each forwards via the function-level
identity plus a single `rfl`-style application.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vec-applied: `pullback f (n • (η + ζ)) x v = n • (pullbacks summed) x v`. -/
@[simp] theorem pullbackFormsLinearMap_nsmul_add_apply_vec
    (f : X → Y) (n : ℕ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • (η + ζ)) x v =
      n • (pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_nsmul_add]; rfl

/-- Vec-applied: `pullback f (n • (η - ζ)) x v` (ℕ). -/
@[simp] theorem pullbackFormsLinearMap_nsmul_sub_apply_vec
    (f : X → Y) (n : ℕ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • (η - ζ)) x v =
      n • (pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_nsmul_sub]; rfl

/-- Vec-applied: `pullback f (n • (η + ζ)) x v` (ℤ). -/
@[simp] theorem pullbackFormsLinearMap_zsmul_add_apply_vec
    (f : X → Y) (n : ℤ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • (η + ζ)) x v =
      n • (pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_zsmul_add]; rfl

/-- Vec-applied: `pullback f (n • (η - ζ)) x v` (ℤ). -/
@[simp] theorem pullbackFormsLinearMap_zsmul_sub_apply_vec
    (f : X → Y) (n : ℤ) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (n • (η - ζ)) x v =
      n • (pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v) := by
  rw [pullbackFormsLinearMap_zsmul_sub]; rfl

end JacobianChallenge.TraceDegree
