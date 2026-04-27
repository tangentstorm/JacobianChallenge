import Jacobian.TraceDegree.PullbackFunSimpApply
import Jacobian.TraceDegree.PullbackFunAddSubApply

/-!
# Vector-apply forms of `pullbackFormsFun` linearity

Vector-apply (`x v`) forms of the pointwise linearity simp lemmas
for `pullbackFormsFun`. Each is `rw + rfl` from the corresponding
point-apply form.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vector-apply: pullback of zero is zero. -/
@[simp] theorem pullbackFormsFun_zero_apply_vec
    (f : X → Y) (x : X) (v : E) :
    pullbackFormsFun f (0 : HolomorphicOneForm E Y) x v = 0 := by
  rw [pullbackFormsFun_zero_apply]; rfl

/-- Vector-apply: pullback of `-η` negates. -/
@[simp] theorem pullbackFormsFun_neg_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f (-η) x v = - (pullbackFormsFun f η x v) := by
  rw [pullbackFormsFun_neg_apply]; rfl

/-- Vector-apply: pullback distributes over addition. -/
@[simp] theorem pullbackFormsFun_add_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f (η + ζ) x v =
      pullbackFormsFun f η x v + pullbackFormsFun f ζ x v := by
  rw [pullbackFormsFun_add_apply]; rfl

/-- Vector-apply: pullback distributes over subtraction. -/
@[simp] theorem pullbackFormsFun_sub_apply_vec
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f (η - ζ) x v =
      pullbackFormsFun f η x v - pullbackFormsFun f ζ x v := by
  rw [pullbackFormsFun_sub_apply]; rfl

/-- Vector-apply: pullback is ℂ-linear. -/
@[simp] theorem pullbackFormsFun_smul_apply_vec
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f (k • η) x v = k • (pullbackFormsFun f η x v) := by
  rw [pullbackFormsFun_smul_apply]; rfl

end JacobianChallenge.TraceDegree
