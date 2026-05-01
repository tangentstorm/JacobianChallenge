import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.CanonicalDivisor

/-!
# Genus identification: analytic ↔ cohomological

Frontier statement of the classical equivalence

  analyticGenus ℂ X = dim_ℂ H⁰(X, K_X) = RSGenus X

between three project-side definitions of the genus of a compact
Riemann surface:

* **analytic** — `analyticGenus ℂ X = Module.finrank ℂ (HolomorphicOneForm ℂ X)`
  (production-side, sorry-free in `AnalyticGenus.lean`);
* **cohomological-via-K_X** — `dim_ℂ H⁰(X, K_X)` where `K_X` is the
  dualizing sheaf;
* **cohomological-via-𝒪_X** — `RSGenus X` (defined as
  `dim_ℂ H¹(X, 𝒪_X)` morally; currently a frontier sorry in
  `EulerCharLineBundle.lean`).

The two cohomological identifications are dual:

  dim H⁰(K_X) = dim H¹(𝒪_X)

via Serre duality (`SerreDualityRS.lean`); the analytic identification

  analyticGenus = dim H⁰(K_X)

is the standard "holomorphic 1-form = global section of the cotangent
sheaf" correspondence (Dolbeault `H^{1,0} = H¹(𝒪)*`-type identity).

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 inventory, the analytic-side
machinery is ABSENT:

* sheaf-of-holomorphic-1-forms = `K_X` realisation,
* the Dolbeault / Hodge identification,
* Serre duality for H¹(𝒪_X) ≃ H⁰(K_X)*.

Both bridging theorems are therefore frontier sorries here. The
**concrete** cohomological-genus def is sorry-free.

## What this file provides

* `cohomologicalGenusH0KX X` — concrete `def` (no sorry):
  `Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)`.
* `analyticGenus_eq_cohomological_genus_h0_KX` — frontier theorem
  (sorry) asserting `analyticGenus ℂ X = dim H⁰(X, K_X)`.
* `RSGenus_eq_analyticGenus` — frontier theorem (sorry) asserting
  `RSGenus X = analyticGenus ℂ X`.

## What this file does NOT provide

* discharge of either bridging theorem (both frontier sorries),
* the explicit Dolbeault decomposition or Serre-duality witness,
* the pushforward `HolomorphicOneForm ℂ X →ₗ[ℂ] H⁰(X, K_X)`
  isomorphism — that map exists abstractly via the cotangent-sheaf
  identification but requires the analytic structure sheaf to make
  precise.

These belong to follow-up nodes once the analytic-sheaf machinery
lands.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- The `H⁰`-cohomological genus, defined as
`Module.finrank ℂ H⁰(X, K_X)` via the project-side `RSDualizingSheaf`
and `RSSheafCohomology` API.

Concrete (no sorry); the upstream frontier-`sorry` on
`RSDualizingSheaf` propagates through, but this derived definition
itself does not introduce any new sorry. The `[Module ℂ …]`
instance argument is required by `Module.finrank` and is consumer-
supplied (see `EulerCharLineBundle.lean` for rationale). -/
noncomputable def cohomologicalGenusH0KX
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf.{_, 0} X) 0)] : ℕ :=
  Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf.{_, 0} X) 0)

/-- **Frontier theorem (sorry).** Analytic genus equals the
cohomological genus via the canonical bundle:

  analyticGenus ℂ X = dim_ℂ H⁰(X, K_X).

PROOF SKETCH (sorry pending the analytic frontier):
1. Identify `HolomorphicOneForm ℂ X` with global sections of the
   cotangent sheaf `K_X` (Dolbeault `H^{1,0}(X) ≃ H⁰(X, K_X)`).
2. Take `Module.finrank ℂ` on both sides.

The proof is `sorry` because the canonical "holomorphic 1-form ↔
section of K_X" isomorphism requires the analytic structure sheaf
`𝒪_X` and the Dolbeault correspondence, both ABSENT in Mathlib
v4.28.0. -/
theorem analyticGenus_eq_cohomological_genus_h0_KX
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf.{_, 0} X) 0)] :
    analyticGenus ℂ X = cohomologicalGenusH0KX X := by
  sorry

/-- **Frontier theorem (sorry).** The cohomological-via-𝒪_X genus
`RSGenus` equals the analytic genus.

PROOF SKETCH (sorry pending the analytic frontier):
1. By Serre duality (`SerreDualityRS.lean`),
   `dim_ℂ H¹(X, 𝒪_X) = dim_ℂ H⁰(X, K_X)`.
2. By the Dolbeault identification
   (`analyticGenus_eq_cohomological_genus_h0_KX` above),
   `dim_ℂ H⁰(X, K_X) = analyticGenus ℂ X`.
3. `RSGenus X` is defined as `dim_ℂ H¹(X, 𝒪_X)`
   (frontier sorry in `EulerCharLineBundle.lean`).
4. Combine.

`sorry` because each of (1), (2), (3) is itself a frontier sorry. -/
theorem RSGenus_eq_analyticGenus
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    RSGenus X = analyticGenus ℂ X := by
  sorry

end JacobianChallenge.HolomorphicForms
