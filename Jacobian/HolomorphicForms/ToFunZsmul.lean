import Jacobian.HolomorphicForms.EvalLinearMapZsmul
import Jacobian.HolomorphicForms.ToFunApplyVecExtra

/-!
# Integer-scalar `toFun` extras

`zsmul_toFun_apply` (in `EvalLinearMapZsmul`) handles the
function-level case. This file completes the picture with the
vec-applied form and a couple of zero-form / double-negation
collapses.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Vec-apply form of `zsmul_toFun_apply`. -/
@[simp] theorem zsmul_toFun_apply_vec
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) (v : E) :
    (n • η).toFun x v = n • (η.toFun x v) := by
  rw [zsmul_toFun_apply]; rfl

/-- `n • η - n • η = 0` at the `toFun` projection, for `n : ℕ`. -/
theorem nsmul_sub_self_toFun_apply
    (n : ℕ) (η : HolomorphicOneForm E X) (x : X) :
    (n • η - n • η).toFun x = 0 := by
  rw [sub_self, zero_toFun_apply]

/-- `n • η - n • η = 0` at the `toFun` projection, for `n : ℤ`. -/
theorem zsmul_sub_self_toFun_apply
    (n : ℤ) (η : HolomorphicOneForm E X) (x : X) :
    (n • η - n • η).toFun x = 0 := by
  rw [sub_self, zero_toFun_apply]

/-- Double-negation collapse at `toFun`. -/
@[simp] theorem neg_neg_toFun_apply
    (η : HolomorphicOneForm E X) (x : X) :
    (- -η).toFun x = η.toFun x := by
  rw [neg_neg]

end JacobianChallenge.HolomorphicForms
