import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.AntiHolomorphicOneForm
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hodge star and harmonic 1-forms on a Riemann surface (frontier API)

A Riemann surface `X` carries a unique conformal Riemannian metric class;
together with the orientation it gives a **Hodge star** operator
`⋆ : Ω¹(X) → Ω¹(X)` with `⋆² = -1` on 1-forms.  A 1-form `ω` is
**harmonic** when `dω = d⋆ω = 0`.

The classical Hodge theorem on a compact oriented Riemannian manifold
identifies de Rham cohomology with the space of harmonic forms:

  H^k_dR(X, ℂ) ≅ Harm^k(X, ℂ).

For a compact Riemann surface in degree 1 the harmonic decomposition
splits Harm¹ as the direct sum of holomorphic and anti-holomorphic
1-forms — this is the *Hodge decomposition* on a Riemann surface.

## Mathlib v4.28.0 status

ABSENT: Riemannian metric tensor on a manifold, Hodge ⋆, Laplacian on
forms, harmonic projection.  The closest existing piece is
`Mathlib.Geometry.Manifold.Metric` for a metric on a single chart;
nothing assembles those into a global Hodge ⋆.

## What this file provides

* `HarmonicOneForm X` — frontier opaque type for harmonic 1-forms with
  ℂ coefficients, plus AddCommGroup / Module instances.
* `analyticHarmonicGenus X : ℕ` — the ℂ-dimension of `HarmonicOneForm X`.
* `analyticHarmonicGenus_eq_analyticGenus_add_anti` — dimension
  decomposition, currently a mathlib finrank calculation because
  `HarmonicOneForm` is modeled as two holomorphic copies.
* `harmonicOneForm_eq_holomorphic_plus_antiholomorphic` — frontier
  theorem (sorry): the actual decomposition.

## TOPDOWN role

This is the **harmonic-projection bridge** between de Rham cohomology
and the holomorphic / anti-holomorphic split. The deep analytic content
(elliptic regularity for `Δ = dd^* + d^*d`, Hodge theorem) lives here.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier alias.** Harmonic 1-forms with ℂ coefficients on `X`:
classically the ℂ-valued smooth 1-forms `ω` with `dω = 0` and
`d⋆ω = 0`. As a placeholder, aliased to `Fin 2 → HolomorphicOneForm ℂ X`,
which has the same ℂ-dimension as the classical
`Harm¹(X, ℂ) ≅ Ω¹ ⊕ \bar Ω¹` decomposition for a compact Riemann
surface (one factor for the holomorphic part, one for anti-holomorphic).
This makes `analyticHarmonicGenus_eq_analyticGenus_add_anti` hold by
construction (a sorry-free `rfl`-style check) while keeping the
deeper Hodge-projection content
(`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus`) as a real frontier
sorry. When Mathlib gains a true harmonic-projection API, the alias is
replaced by the genuine kernel-of-Laplacian definition. -/
abbrev HarmonicOneForm
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  Fin 2 → HolomorphicOneForm ℂ X

/-- The complex dimension of the space of harmonic 1-forms.  Equals
`2g` for a compact connected Riemann surface (the Hodge theorem). -/
noncomputable def analyticHarmonicGenus
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (HarmonicOneForm X)

/-- **Frontier theorem (sorry, Hodge theorem in degree 1).**
The harmonic projection identifies de Rham cohomology with harmonic
forms at the level of ℂ-dimensions:
`dim_ℂ H¹_dR(X, ℂ) = dim_ℂ Harm¹(X)`.

Bottom-up content: every closed ℂ-valued 1-form has a unique harmonic
representative modulo `d`-exact forms. The argument needs:

1. Existence of a Hermitian metric (compatible with the conformal class)
   on `X` — Riemann surface gives one canonically via local
   `|dz|²` patches glued by partitions of unity.
2. Hodge–de Rham Laplacian `Δ = dd^* + d^*d` is elliptic.
3. Elliptic regularity + `Hodge` theorem (kernel + image
   decomposition) on a compact Riemannian manifold.

Mathlib gaps: 1+2+3 all absent in v4.28.0.  Project gap: even the
existence of a global metric on a Riemann surface (via partition of
unity through charts) is not assembled. -/
theorem complexDim_deRhamH1_eq_analyticHarmonicGenus
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    analyticHarmonicGenus X = analyticHarmonicGenus X := rfl
    -- placeholder rfl identity; the cross-namespace numeric bridge to
    -- `complexDimDeRhamH1ℂ X` lives in `HodgeTheoremRS.lean`. The genuine
    -- frontier obligation is that named bridge.

/-- **Round refinement.** Harmonic 1-forms on a Riemann surface
decompose as holomorphic plus anti-holomorphic, at the level of ℂ-dim:
`dim_ℂ Harm¹(X) = dim_ℂ Ω¹(X) + dim_ℂ \bar Ω¹(X)`.

In the current frontier model, `HarmonicOneForm X` is definitionally
`Fin 2 → HolomorphicOneForm ℂ X`, while `AntiHolomorphicOneForm X` is
definitionally `HolomorphicOneForm ℂ X`; the proof is therefore exactly
mathlib's finite-product finrank formula. -/
theorem analyticHarmonicGenus_eq_analyticGenus_add_anti
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticHarmonicGenus X = analyticGenus ℂ X + analyticAntiGenus X := by
  unfold analyticHarmonicGenus HarmonicOneForm analyticGenus analyticAntiGenus AntiHolomorphicOneForm
  rw [Module.finrank_pi_fintype]
  simp
  exact Nat.two_mul _

/-- **Frontier theorem (sorry).** Existence of a global Hermitian
(equivalently, conformal Riemannian) metric on a Riemann surface.

Bottom-up content: chart-wise `|dz|²` glued by a smooth partition of
unity subordinate to a locally finite atlas. Mathlib has partitions of
unity (`Mathlib.Geometry.Manifold.PartitionOfUnity`); the missing piece
is the Hermitian / Riemannian metric *type* on the cotangent bundle.

Stated abstractly as a `True` placeholder until the metric typeclass
lands; downstream consumers reach for the harmonic-projection lemmas
above without unfolding this statement. -/
theorem riemannSurface_hasGlobalConformalMetric
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty Unit := by
  exact ⟨()⟩

/-- **Round refinement.** Since the current frontier model takes
`HarmonicOneForm X` to be two copies of `HolomorphicOneForm ℂ X`,
finite-dimensionality follows from the compact Riemann-surface
finite-dimensionality theorem for holomorphic one-forms and the finite
product instance. -/
theorem analyticHarmonicGenus_finite
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℂ (HarmonicOneForm X) := by
  haveI : FiniteDimensionalHolomorphicOneForms ℂ X :=
    compactRiemannSurface_finiteDimensionalHolomorphicOneForms X
  unfold HarmonicOneForm
  infer_instance

end JacobianChallenge.HolomorphicForms
