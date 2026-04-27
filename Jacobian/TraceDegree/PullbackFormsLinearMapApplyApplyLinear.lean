import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear
import Jacobian.TraceDegree.PullbackFunSimpApplyVec

/-!
# Bundled vector-apply linearity for `pullbackFormsLinearMap`

Vector-apply (`x v`) forms of the bundled-LinearMap-level linearity
simp lemmas. Lifted via `pullbackFormsLinearMap_apply_at`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Bundled vector-apply: zero pullback. -/
@[simp] theorem pullbackFormsLinearMap_zero_apply_vec
    (f : X → Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (0 : HolomorphicOneForm E Y) x v = 0 := by
  rw [pullbackFormsLinearMap_zero_apply]; rfl

/-- Bundled vector-apply: negation. -/
@[simp] theorem pullbackFormsLinearMap_neg_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (-η) x v =
      - (pullbackFormsLinearMap f η x v) := by
  rw [pullbackFormsLinearMap_neg_apply]; rfl

/-- Bundled vector-apply: addition. -/
@[simp] theorem pullbackFormsLinearMap_add_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η + ζ) x v =
      pullbackFormsLinearMap f η x v +
        pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_add_apply]; rfl

/-- Bundled vector-apply: subtraction. -/
@[simp] theorem pullbackFormsLinearMap_sub_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (η - ζ) x v =
      pullbackFormsLinearMap f η x v -
        pullbackFormsLinearMap f ζ x v := by
  rw [pullbackFormsLinearMap_sub_apply]; rfl

/-- Bundled vector-apply: scalar multiplication. -/
@[simp] theorem pullbackFormsLinearMap_smul_apply_vec
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f (k • η) x v =
      k • (pullbackFormsLinearMap f η x v) := by
  rw [pullbackFormsLinearMap_smul_apply]; rfl

end JacobianChallenge.TraceDegree
