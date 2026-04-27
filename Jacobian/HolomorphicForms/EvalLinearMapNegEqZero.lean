import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# `evalLinearMap` negation zero-iff

`evalLinearMap x v (-η) = 0` iff `evalLinearMap x v η = 0`.
Direct corollary of `(evalLinearMap x v).map_neg`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `evalLinearMap x v (-η) = 0` iff `evalLinearMap x v η = 0`. -/
theorem evalLinearMap_neg_eq_zero_iff
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (-η) = 0 ↔ evalLinearMap x v η = 0 := by
  sorry

end JacobianChallenge.HolomorphicForms
