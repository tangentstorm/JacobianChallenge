import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.PeriodFunctional
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.FiniteDimensional
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Stage B umbrella: analytic genus equals topological genus

This file states the **Stage B** obligation of
`ref/plans/polygonal-model.md`: on a compact connected Riemann surface,
the analytic genus (dimension of the space of holomorphic 1-forms)
equals the topological genus (half the ℤ-rank of singular `H₁`).

## Top-down role

The umbrella theorem `analyticGenus_eq_topologicalGenus` is the named
obligation that `polygonal_model` delegates to in order to translate
between the analytic genus that appears in the challenge hypothesis and
the topological genus that appears in the conclusion of Stage A.

After Round 26 unification, the umbrella *is* the same declaration as
`JacobianChallenge.Periods.analyticGenus_eq_topologicalGenus` defined in
`Jacobian.Periods.PeriodFunctional` (re-exported through the import
above) — both share the canonical
`JacobianChallenge.Periods.topologicalGenus` from
`Jacobian.Periods.TopologicalGenus`.

## Stage B leaves

This file additionally factors the Stage B work into two precise leaves
*on top of* the canonical umbrella, with a meet-in-the-middle discharge
of the structural-iso leaf via the project's existing
`h1_basis_of_compact_riemann_surface`:

* `singularH1_compactRiemannSurface_iso_freeZ` (**real proof**) — the
  ℤ-linear iso `singularH1 X ≃ₗ[ℤ] (Fin (2 * analyticGenus ℂ X) → ℤ)`,
  produced by `b.equivFun` on the basis from
  `h1_basis_of_compact_riemann_surface`. This was the Stage B
  structural sorry; it is now discharged.
* `singularH1_finrank_eq_two_mul_analyticGenus` (**real proof**) —
  rank statement, derived from the iso via `LinearEquiv.finrank_eq` +
  `Module.finrank_pi` + `Fintype.card_fin`.

The remaining Stage B sorry is one level lower at
`Jacobian.Periods.PeriodFunctional.h1_has_even_basis`
(or equivalently `hodge_deRham_rank_eq`), where the Hodge / de Rham +
Riemann–Roch / period-lattice analytic content lives.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Stage B structural leaf (real proof, meet-in-the-middle).** On a
compact connected Riemann surface, singular `H₁(X, ℤ)` is ℤ-linearly
isomorphic to the free module of rank `2g`, where `g = analyticGenus ℂ X`.

Body: extract the basis from
`JacobianChallenge.Periods.h1_basis_of_compact_riemann_surface`
(in `Jacobian.Periods.PeriodFunctional`) and turn it into a linear
equivalence via `Basis.equivFun`. Uses `singularH1 X = IntegralOneCycle X`
(definitionally, by abbrev) so no transport lemma is needed. -/
theorem singularH1_compactRiemannSurface_iso_freeZ
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (singularH1 X ≃ₗ[ℤ] (Fin (2 * analyticGenus ℂ X) → ℤ)) := by
  obtain ⟨b⟩ := h1_basis_of_compact_riemann_surface X
  exact ⟨b.equivFun⟩

/-- **Stage B leaf.** On a compact connected Riemann surface,
the ℤ-rank of singular `H₁` equals `2g` where `g = analyticGenus ℂ X`.

Body: lift through `singularH1_compactRiemannSurface_iso_freeZ` to
the free ℤ-module `Fin (2g) → ℤ`, then compute via
`LinearEquiv.finrank_eq`, `Module.finrank_pi`, and `Fintype.card_fin`.

Both sub-steps are real proofs; the only remaining analytic content
sits below in `PeriodFunctional.h1_has_even_basis`. -/
theorem singularH1_finrank_eq_two_mul_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Module.finrank ℤ (singularH1 X) = 2 * analyticGenus ℂ X := by
  obtain ⟨e⟩ := singularH1_compactRiemannSurface_iso_freeZ X
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_fin]

end JacobianChallenge.Periods
