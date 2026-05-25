import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Extra `evalLinearMap` API: at-point forms via `LinearMap` interface

Small named wrappers exposing the `LinearMap`-inherited identities
on `evalLinearMap` at the function level — useful when the caller
already has the form `evalLinearMap x v` in scope and wants to
apply standard linear-map rewrites without unfolding.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
`evalLinearMap x v` at the form `0` is `0` — `LinearMap.map_zero`
form.
-/
theorem evalLinearMap_apply_zero (x : X) (v : E) :
    evalLinearMap (E := E) (X := X) x v 0 = 0 :=
  (evalLinearMap x v).map_zero

/-- `evalLinearMap x v` at `η + ζ` distributes — `LinearMap.map_add` form. -/
theorem evalLinearMap_apply_add
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v (η + ζ) =
      evalLinearMap x v η + evalLinearMap x v ζ :=
  (evalLinearMap x v).map_add η ζ

/-- `evalLinearMap x v` at `-η` negates — `LinearMap.map_neg` form. -/
theorem evalLinearMap_apply_neg
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (-η) = -evalLinearMap x v η :=
  (evalLinearMap x v).map_neg η

/-- `evalLinearMap x v` at `η - ζ` distributes — `LinearMap.map_sub` form. -/
theorem evalLinearMap_apply_sub
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v (η - ζ) =
      evalLinearMap x v η - evalLinearMap x v ζ :=
  (evalLinearMap x v).map_sub η ζ

end JacobianChallenge.HolomorphicForms
