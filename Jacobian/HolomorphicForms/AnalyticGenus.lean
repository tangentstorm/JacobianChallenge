import Jacobian.HolomorphicForms.FiniteDimensional

/-!
# Small `analyticGenus` API

Convenience simp lemmas exposing `analyticGenus` as `Module.finrank`,
plus the basic equivalence with subsingleton-ness of the form space.

These are pure rfl/`finrank` rewrites — useful for downstream callers
that want to reason about the dimension without unfolding the
definition.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

/-- `analyticGenus` unfolds to `Module.finrank`. -/
@[simp] theorem analyticGenus_def :
    analyticGenus E X = Module.finrank ℂ (HolomorphicOneForm E X) := rfl

/-- `analyticGenus = 0` iff the form space has finrank 0. -/
theorem analyticGenus_eq_zero_iff_finrank_zero :
    analyticGenus E X = 0 ↔
      Module.finrank ℂ (HolomorphicOneForm E X) = 0 := Iff.rfl

/-- `analyticGenus = 0` iff the form space is `Subsingleton`. -/
theorem analyticGenus_eq_zero_iff_subsingleton :
    analyticGenus E X = 0 ↔ Subsingleton (HolomorphicOneForm E X) := by
  rw [analyticGenus_eq_zero_iff_finrank_zero]
  exact Module.finrank_zero_iff

/-- If the form space is `Subsingleton`, the analytic genus is zero. -/
theorem analyticGenus_eq_zero_of_subsingleton
    [Subsingleton (HolomorphicOneForm E X)] : analyticGenus E X = 0 :=
  analyticGenus_eq_zero_iff_subsingleton.mpr ‹_›

end JacobianChallenge.HolomorphicForms
