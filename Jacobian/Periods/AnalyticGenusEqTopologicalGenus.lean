import Jacobian.Periods.TopologicalGenus
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.FiniteDimensional

/-!
# Stage B umbrella: analytic genus equals topological genus

This file states the **Stage B** obligation of
`ref/plans/polygonal-model.md`: on a compact connected Riemann surface,
the analytic genus (dimension of the space of holomorphic 1-forms)
equals the topological genus (half the ℤ-rank of singular `H₁`).

## Top-down role

`analyticGenus_eq_topologicalGenus` is the named obligation that the
umbrella `polygonal_model` delegates to in order to translate between
the analytic genus that appears in the challenge hypothesis and the
topological genus that appears in the conclusion of Stage A.

## Bottom-up content

Two classical proof routes are available:

* **Hodge route.** `H¹(X, ℝ) ≃ H^{1,0}(X) ⊕ H^{0,1}(X)` with
  `dim H^{1,0} = dim H^{0,1} = g`. This requires Dolbeault cohomology
  on Riemann surfaces, which Mathlib v4.28.0 lacks.
* **De Rham + Riemann–Roch route.** Combine Stokes-on-RS with
  Riemann–Roch (planned in `ref/plans/stokes-on-rs-with-boundary.md`
  and `input:riemann-roch`) to compare `H¹_{dR}` and `H⁰(K)`.

Each is a ~1000–2000 LOC project on top of substantial Mathlib
prerequisites; the bridge sits below this named statement.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Stage B umbrella.** On a compact connected Riemann surface,
`analyticGenus ℂ X = topologicalGenus X`.

The right-hand side is `Module.finrank ℤ H₁(X, ℤ) / 2` from
`Jacobian.Periods.TopologicalGenus`; the left-hand side is the
holomorphic-form dimension from `Jacobian.HolomorphicForms`. The
identity is the analytic↔topological genus bridge required by
the polygonal-model assembly. -/
theorem analyticGenus_eq_topologicalGenus
    (X : Type) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = topologicalGenus X := by
  sorry

end JacobianChallenge.Periods
