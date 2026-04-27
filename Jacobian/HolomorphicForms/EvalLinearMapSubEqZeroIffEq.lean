import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# `evalLinearMap` sub-zero ↔ equality

`evalLinearMap x v (η - ζ) = 0` iff
`evalLinearMap x v η = evalLinearMap x v ζ`. Direct corollary of
`(evalLinearMap x v).map_sub` plus the standard `sub_eq_zero` ↔
`a = b` characterization.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `evalLinearMap x v (η - ζ) = 0` iff
`evalLinearMap x v η = evalLinearMap x v ζ`. -/
theorem evalLinearMap_sub_eq_zero_iff_eq
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v (η - ζ) = 0 ↔
      evalLinearMap x v η = evalLinearMap x v ζ := by
  rw [(evalLinearMap x v).map_sub, sub_eq_zero]

end JacobianChallenge.HolomorphicForms
