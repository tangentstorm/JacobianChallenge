import Jacobian.HolomorphicForms.HodgeStarRS
import Jacobian.HolomorphicForms.AntiHolomorphicOneForm
import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Hodge decomposition dimension formula on a Riemann surface (frontier)

Assembled frontier identity: for a compact connected Riemann surface
`X` of analytic genus `g`,

  dim_ℂ H¹_dR(X, ℂ) = 2 g.

The classical proof routes through the *harmonic decomposition*:

  H¹_dR(X, ℂ) ≅ Harm¹(X)
              = Ω¹(X)_holo ⊕ Ω¹(X)_anti
              ≅ ℂ^g ⊕ ℂ^g.

The conjugation isomorphism on `Ω¹(X)_anti ≃ Ω¹(X)_holo` (as ℝ-vector
spaces) gives `dim_ℂ Ω¹_anti = g`, so the total dim is `2g`.

## Mathlib v4.28.0 status

Each ingredient is a frontier sorry:

* harmonic projection (`HodgeStarRS.lean`),
* anti-holomorphic conjugation (`AntiHolomorphicOneForm.lean`),
* `\bar Ω¹` finite-dim (`AntiHolomorphicOneForm.lean`).

This file performs the **arithmetic assembly** and is sorry-free
relative to its named obligations.

## What this file provides

* `complexDim_deRhamH1ℂ_eq_two_analyticGenus` — frontier theorem,
  *sorry-free assembly* of the named harmonic-projection and
  conjugation obligations.

* `complexDim_deRhamH1ℂ_eq_two_analyticGenus_via_harmonic` — the same
  identity stated as the explicit `2 * analyticGenus ℂ X` (RHS form
  consumed by the top-level `hodge_deRham_rank_eq` assembly).

## TOPDOWN role

This is the **Hodge side** of the dimension chain:
`2g = dim_ℂ Ω¹ + dim_ℂ \bar Ω¹ = dim_ℂ Harm¹ = dim_ℂ H¹_dR`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier theorem (sorry).** Bridge between the harmonic space and
the de Rham H¹: `dim_ℂ H¹_dR(X, ℂ) = analyticHarmonicGenus X`.

This is the named numeric form of the Hodge harmonic-projection
isomorphism (`complexDim_deRhamH1_eq_analyticHarmonicGenus` in
`HodgeStarRS.lean` is currently an `rfl` placeholder; the *real* bridge
lives here). -/
theorem complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = analyticHarmonicGenus X := by
  sorry

/-- **Sorry-free arithmetic.** From the conjugation isomorphism and
the Hodge harmonic decomposition,

  analyticHarmonicGenus X = 2 * analyticGenus ℂ X.

Combines `analyticHarmonicGenus_eq_analyticGenus_add_anti` and
`analyticAntiGenus_eq_analyticGenus`. Pure `omega` after rewriting. -/
theorem analyticHarmonicGenus_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticHarmonicGenus X = 2 * analyticGenus ℂ X := by
  rw [analyticHarmonicGenus_eq_analyticGenus_add_anti X,
      analyticAntiGenus_eq_analyticGenus X]
  ring

/-- **Hodge side, sorry-free assembly.** Complex dimension of H¹_dR on
a compact connected Riemann surface equals twice the analytic genus.

Combines `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (harmonic
projection) and `analyticHarmonicGenus_eq_two_analyticGenus`
(harmonic = holo + anti-holo, conjugation). -/
theorem complexDimDeRhamH1ℂ_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    complexDimDeRhamH1ℂ X = 2 * analyticGenus ℂ X := by
  rw [complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus X,
      analyticHarmonicGenus_eq_two_analyticGenus X]

/-- **Hodge side, sorry-free assembly.** Real dimension of H¹_dR on a
compact connected Riemann surface equals `2g`. The form of the identity
the top-level `hodge_deRham_rank_eq` assembly consumes.

Combines:
* `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (real-of-complex equality,
  in `DeRhamCohomology.lean`),
* `complexDimDeRhamH1ℂ_eq_two_analyticGenus` (Hodge decomp + conjugation,
  in this file). -/
theorem realDimDeRhamH1_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    realDimDeRhamH1 X = 2 * analyticGenus ℂ X := by
  rw [realDim_deRhamH1_eq_complexDim_deRhamH1ℂ X,
      complexDimDeRhamH1ℂ_eq_two_analyticGenus X]

end JacobianChallenge.HolomorphicForms
