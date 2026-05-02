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

Refined into a single named ℤ-rank leaf:

* `singularH1_finrank_eq_two_mul_analyticGenus` — for a compact
  connected Riemann surface `X`,
  `Module.finrank ℤ (singularH1 X) = 2 * analyticGenus ℂ X`.

The umbrella body just unfolds `topologicalGenus`, rewrites by the
leaf, and divides by 2.

## Bottom-up content of the leaf

Two classical proof routes are available:

* **Hodge route.** `H¹(X, ℝ) ≃ H^{1,0}(X) ⊕ H^{0,1}(X)` with
  `dim H^{1,0} = dim H^{0,1} = g`. This requires Dolbeault cohomology
  on Riemann surfaces, which Mathlib v4.28.0 lacks.
* **De Rham + Riemann–Roch route.** Combine Stokes-on-RS with
  Riemann–Roch (planned in `ref/plans/stokes-on-rs-with-boundary.md`
  and `input:riemann-roch`) to compare `H¹_{dR}` and `H⁰(K)`.
* **Period-lattice route (project-internal).** The project's
  `periodSubgroup` is a `ℤ`-lattice of rank `2g` inside
  `HolomorphicOneFormDual ℂ X`; singular `H₁` maps isomorphically
  onto it (period pairing). Rank-of-period-lattice computations live
  in `Jacobian.Periods.PeriodFunctional`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier structural leaf.** On a compact connected Riemann
surface, singular `H₁(X, ℤ)` is ℤ-linearly isomorphic to the free
module of rank `2g`, where `g = analyticGenus ℂ X`.

Bottom-up routes:

* **Hodge route.** `H¹(X, ℝ) ≃ H^{1,0}(X) ⊕ H^{0,1}(X)` with
  `dim H^{1,0} = dim H^{0,1} = g`. Requires Dolbeault cohomology
  (Mathlib v4.28.0 gap).
* **De Rham + Riemann–Roch route.** Combine Stokes-on-RS with
  Riemann–Roch (planned in `ref/plans/stokes-on-rs-with-boundary.md`
  and `input:riemann-roch`).
* **Period-lattice route (project-internal).** The project's
  `periodSubgroup` is a `ℤ`-lattice of rank `2g` inside
  `HolomorphicOneFormDual ℂ X`; singular `H₁` maps isomorphically
  onto it via the period pairing. See
  `Jacobian.Periods.PeriodFunctional` (`h1_basis_of_compact_riemann_surface`,
  `periodSubgroup_isZLattice`) for the existing project hooks.

**Note (meet-in-the-middle).** The project's
`h1_basis_of_compact_riemann_surface` already gives a ℤ-basis of
`IntegralOneCycle X = singularH1 X` (modulo `ModuleCat ℤ` coercion)
indexed by `Fin (2 * analyticGenus ℂ X)`. That basis lifts directly
to the linear iso required here once the duplicate `topologicalGenus`
definition between `TopologicalGenus.lean` and `PeriodFunctional.lean`
is reconciled. -/
theorem singularH1_compactRiemannSurface_iso_freeZ
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (singularH1 X ≃ₗ[ℤ] (Fin (2 * analyticGenus ℂ X) → ℤ)) := by
  sorry

/-- **Stage B leaf.** On a compact connected Riemann surface,
the ℤ-rank of singular `H₁` equals `2g` where `g = analyticGenus ℂ X`.

Body: lift through `singularH1_compactRiemannSurface_iso_freeZ` to
the free ℤ-module `Fin (2g) → ℤ`, then compute via
`LinearEquiv.finrank_eq`, `Module.finrank_pi`, and `Fintype.card_fin`. -/
theorem singularH1_finrank_eq_two_mul_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Module.finrank ℤ (singularH1 X) = 2 * analyticGenus ℂ X := by
  obtain ⟨e⟩ := singularH1_compactRiemannSurface_iso_freeZ X
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- **Stage B umbrella.** On a compact connected Riemann surface,
`analyticGenus ℂ X = topologicalGenus X`.

Body: unfold `topologicalGenus = finrank ℤ singularH1 / 2`, rewrite
through `singularH1_finrank_eq_two_mul_analyticGenus`, and divide
`2 * g` by `2`. -/
theorem analyticGenus_eq_topologicalGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = topologicalGenus X := by
  unfold JacobianChallenge.Periods.topologicalGenus
  rw [singularH1_finrank_eq_two_mul_analyticGenus X,
      Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]

end JacobianChallenge.Periods
