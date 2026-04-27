import Jacobian.TraceDegree.PullbackFunEvalLinearMap

/-!
# Pullback-along-id ↔ `evalLinearMap` characterizations

A small follow-up to `PullbackFunEvalLinearMap` covering the trivial
`f = id` corner: its pullback collapses to the bundled `evalLinearMap`
in clean ways.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Pullback along `id` evaluated at `x v` matches `evalLinearMap x v η`. -/
theorem pullbackFormsFun_id_apply_vec_eq_evalLinearMap'
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x v = evalLinearMap x v η :=
  pullbackFormsFun_id_apply_vec_eq_evalLinearMap η x v

set_option linter.unusedSectionVars false in
/-- Pullback along `id` is zero at `(x, v)` iff `evalLinearMap x v η = 0`. -/
theorem pullbackFormsFun_id_eq_zero_iff_evalLinearMap_eq_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x v = 0 ↔
      evalLinearMap (E := E) (X := X) x v η = 0 := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap]

set_option linter.unusedSectionVars false in
/-- Two forms have equal pullbacks along `id` (at fixed `x v`) iff their
`evalLinearMap` values coincide. -/
theorem pullbackFormsFun_id_eq_iff_evalLinearMap_eq
    (η ζ : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x v =
      pullbackFormsFun (id : X → X) ζ x v ↔
      evalLinearMap (E := E) (X := X) x v η =
        evalLinearMap x v ζ := by
  rw [pullbackFormsFun_id_apply_vec_eq_evalLinearMap,
      pullbackFormsFun_id_apply_vec_eq_evalLinearMap]

set_option linter.unusedSectionVars false in
/-- Pullback-along-id factors as `evalLinearMap` of `η` evaluated at
`(x, v)`. -/
theorem pullbackFormsFun_id_factor_evalLinearMap
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    pullbackFormsFun (id : X → X) η x v = evalLinearMap x v η :=
  pullbackFormsFun_id_apply_vec_eq_evalLinearMap η x v

end JacobianChallenge.TraceDegree
