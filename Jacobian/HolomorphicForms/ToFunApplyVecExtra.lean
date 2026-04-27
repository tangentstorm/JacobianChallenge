import Jacobian.HolomorphicForms.ToFunApplyVec

/-!
# Remaining vec-apply `toFun` simps (sub, smul) + nat/int smul cases

Closes the vec-apply variants of the pointwise `toFun` matrix:

- `sub_toFun_apply_vec`
- `smul_toFun_apply_vec`
- `nsmul_toFun_apply` and `nsmul_toFun_apply_vec`

Together with `ToFunApply` and `ToFunApplyVec` this covers
zero/neg/add/sub/smul/nsmul at the `toFun` projector at both the
function-level and tangent-vector-applied levels.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem sub_toFun_apply_vec
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    (η - ζ).toFun x v = η.toFun x v - ζ.toFun x v := by
  rw [sub_toFun_apply]; rfl

@[simp] theorem smul_toFun_apply_vec
    (k : ℂ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    (k • η).toFun x v = k • (η.toFun x v) := by
  rw [smul_toFun_apply]; rfl

@[simp] theorem nsmul_toFun_apply
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) :
    (n • η).toFun x = n • (η.toFun x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, add_toFun_apply, ih]

@[simp] theorem nsmul_toFun_apply_vec
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    (n • η).toFun x v = n • (η.toFun x v) := by
  rw [nsmul_toFun_apply]; rfl

end JacobianChallenge.HolomorphicForms
