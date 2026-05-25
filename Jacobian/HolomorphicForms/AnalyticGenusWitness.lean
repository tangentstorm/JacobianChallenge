import Jacobian.HolomorphicForms.AnalyticGenusPos
import Jacobian.HolomorphicForms.ExtEvalLinearMap

/-!
# Witness-driven positivity for `analyticGenus`

Combines `analyticGenus_pos_of_exists_ne_zero` (positivity from a
non-zero form) with `ne_zero_of_evalLinearMap_ne_zero` (a non-zero
`evalLinearMap` value certifies a non-zero form). Yields:

> a single `(x, v, η)` with `evalLinearMap x v η ≠ 0` is enough to
> guarantee `0 < analyticGenus E X`.

Useful when checking the anti-hack `genus_eq_zero_iff_homeo` against
concrete examples.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

/--
Witness positivity: a single non-vanishing `evalLinearMap` value
forces `analyticGenus` to be positive.
-/
theorem analyticGenus_pos_of_evalLinearMap_ne_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E)
    (h : evalLinearMap x v η ≠ 0) : 0 < analyticGenus E X :=
  analyticGenus_pos_of_exists_ne_zero
    ⟨η, ne_zero_of_evalLinearMap_ne_zero η x v h⟩

/--
Witness non-zero: a single non-vanishing `evalLinearMap` value
forces `analyticGenus` to be non-zero.
-/
theorem analyticGenus_ne_zero_of_evalLinearMap_ne_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E)
    (h : evalLinearMap x v η ≠ 0) : analyticGenus E X ≠ 0 :=
  Nat.pos_iff_ne_zero.mp
    (analyticGenus_pos_of_evalLinearMap_ne_zero η x v h)

/-- Witness positivity through `toFun` directly. -/
theorem analyticGenus_pos_of_toFun_ne_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E)
    (h : η.toFun x v ≠ 0) : 0 < analyticGenus E X :=
  analyticGenus_pos_of_evalLinearMap_ne_zero η x v
    (by rwa [evalLinearMap_apply])

set_option linter.unusedSectionVars false in
/--
Convenience: form-level `Nontrivial` from an `evalLinearMap`
witness.
-/
theorem nontrivial_holomorphicOneForm_of_evalLinearMap_ne_zero
    (η : HolomorphicOneForm E X) (x : X) (v : E)
    (h : evalLinearMap x v η ≠ 0) :
    Nontrivial (HolomorphicOneForm E X) :=
  ⟨η, 0, ne_zero_of_evalLinearMap_ne_zero η x v h⟩

end JacobianChallenge.HolomorphicForms
