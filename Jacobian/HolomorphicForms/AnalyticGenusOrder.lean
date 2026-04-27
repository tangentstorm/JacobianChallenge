import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Order/equality helpers for `analyticGenus`

`analyticGenus E X = Module.finrank ℂ (HolomorphicOneForm E X)` by
`rfl`, so `≤`, `<`, `=` between `analyticGenus` and a natural number
all reduce to the same comparison on `Module.finrank`. These small
named helpers make it easy to chain such reductions in `rw` proofs.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

theorem analyticGenus_le_iff_finrank_le (n : ℕ) :
    analyticGenus E X ≤ n ↔
      Module.finrank ℂ (HolomorphicOneForm E X) ≤ n := Iff.rfl

theorem analyticGenus_lt_iff_finrank_lt (n : ℕ) :
    analyticGenus E X < n ↔
      Module.finrank ℂ (HolomorphicOneForm E X) < n := Iff.rfl

theorem analyticGenus_eq_iff_finrank_eq (n : ℕ) :
    analyticGenus E X = n ↔
      Module.finrank ℂ (HolomorphicOneForm E X) = n := Iff.rfl

theorem analyticGenus_ge_iff_finrank_ge (n : ℕ) :
    n ≤ analyticGenus E X ↔
      n ≤ Module.finrank ℂ (HolomorphicOneForm E X) := Iff.rfl

end JacobianChallenge.HolomorphicForms
