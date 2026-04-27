import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# `evalLinearMap` zero-iff bridge

`evalLinearMap x v η = 0` iff the underlying `toFun` value `η.toFun x v`
is zero. Trivial corollary of `evalLinearMap_apply` (which is `rfl`),
exposed as a named iff for downstream rewrites.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `evalLinearMap x v η = 0` iff `η.toFun x v = 0`. -/
theorem evalLinearMap_eq_zero_iff_toFun_eq_zero
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v η = 0 ↔ η.toFun x v = 0 := by
  sorry

end JacobianChallenge.HolomorphicForms
