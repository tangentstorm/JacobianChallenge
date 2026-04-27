import Jacobian.HolomorphicForms.EvalLinearMapEqZero

/-!
# `evalLinearMap` non-zero from `toFun` non-zero

Forward direction of `EvalLinearMapEqZero` as a non-iff statement
suitable for direct application.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- If `η.toFun x v ≠ 0` then `evalLinearMap x v η ≠ 0`. -/
theorem evalLinearMap_ne_zero_of_toFun_ne_zero
    (x : X) (v : E) {η : HolomorphicOneForm E X}
    (h : η.toFun x v ≠ 0) :
    evalLinearMap x v η ≠ 0 := by
  sorry

end JacobianChallenge.HolomorphicForms
