import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Positivity of `analyticGenus`

Equivalences between `0 < analyticGenus E X` and nontriviality of
the form space, plus a witness-driven sufficient condition.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

/-- `0 < analyticGenus` iff the form space is `Nontrivial`. -/
theorem analyticGenus_pos_iff_nontrivial :
    0 < analyticGenus E X ↔ Nontrivial (HolomorphicOneForm E X) := by
  rw [analyticGenus_def]
  exact Module.finrank_pos_iff

/-- `analyticGenus ≠ 0` iff the form space is `Nontrivial`. -/
theorem analyticGenus_ne_zero_iff_nontrivial :
    analyticGenus E X ≠ 0 ↔ Nontrivial (HolomorphicOneForm E X) := by
  rw [← analyticGenus_pos_iff_nontrivial, Nat.pos_iff_ne_zero]

/-- Sufficient witness condition: the existence of a nonzero form
makes `analyticGenus` positive. -/
theorem analyticGenus_pos_of_exists_ne_zero
    (h : ∃ η : HolomorphicOneForm E X, η ≠ 0) :
    0 < analyticGenus E X :=
  analyticGenus_pos_iff_nontrivial.mpr ⟨h.choose, 0, h.choose_spec⟩

/-- Contrapositive: a zero `analyticGenus` forces `Subsingleton`. -/
theorem subsingleton_of_analyticGenus_eq_zero
    (h : analyticGenus E X = 0) : Subsingleton (HolomorphicOneForm E X) :=
  analyticGenus_eq_zero_iff_subsingleton.mp h

end JacobianChallenge.HolomorphicForms
