import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Equality / non-equality iff bridges for `evalLinearMap`

`evalLinearMap x v` agrees on two forms iff their `toFun x v` values
match. Trivial corollaries of `evalLinearMap_apply` (which is `rfl`),
exposed as named iffs for downstream rewrites.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Two `evalLinearMap`s at the same `(x, v)` agree iff the underlying
`toFun x v` values agree.
-/
theorem evalLinearMap_eq_iff_toFun_eq
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v η = evalLinearMap x v ζ ↔
      η.toFun x v = ζ.toFun x v := by
  rw [evalLinearMap_apply, evalLinearMap_apply]

/--
`evalLinearMap x v η ≠ evalLinearMap x v ζ` iff the
`toFun x v` values differ.
-/
theorem evalLinearMap_ne_iff_toFun_ne
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v η ≠ evalLinearMap x v ζ ↔
      η.toFun x v ≠ ζ.toFun x v := by
  rw [ne_eq, ne_eq, evalLinearMap_eq_iff_toFun_eq]

/-- `evalLinearMap x v η ≠ 0` iff `η.toFun x v ≠ 0`. -/
theorem evalLinearMap_ne_zero_iff_toFun_ne_zero
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v η ≠ 0 ↔ η.toFun x v ≠ 0 := by
  rw [ne_eq, ne_eq, evalLinearMap_apply]

/--
Sufficient direction: `η.toFun x v = ζ.toFun x v` ⇒
`evalLinearMap x v η = evalLinearMap x v ζ`.
-/
theorem evalLinearMap_eq_of_toFun_eq
    (x : X) (v : E) {η ζ : HolomorphicOneForm E X}
    (h : η.toFun x v = ζ.toFun x v) :
    evalLinearMap x v η = evalLinearMap x v ζ :=
  (evalLinearMap_eq_iff_toFun_eq x v η ζ).mpr h

end JacobianChallenge.HolomorphicForms
