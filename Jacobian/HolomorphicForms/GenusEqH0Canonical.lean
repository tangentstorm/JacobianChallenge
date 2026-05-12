import Jacobian.HolomorphicForms.GenusIdentification
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Cap of the genus-identification chain: `RSGenus X = h⁰(X, K_X)`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The cohomological-via-𝒪_X genus and the cohomological-via-K_X genus
agree on a compact connected Riemann surface:

  RSGenus X = dim_ℂ H⁰(X, K_X) = cohomologicalGenusH0KX X.

The body of this file is **sorry-free**: it composes two bridging
theorems from `GenusIdentification.lean` (`RSGenus_eq_analyticGenus`
and `analyticGenus_eq_cohomological_genus_h0_KX`). The deep content
remains in those upstream frontier sorries.

## What this file provides

* `RSGenus_eq_h0_KX X` — sorry-free identity
  `RSGenus X = cohomologicalGenusH0KX X`.
* `RSGenus_eq_finrank_h0_KX X` — same identity unfolded to the
  underlying `Module.finrank` of the cohomology group, the form
  most useful to consumers (no need to know about
  `cohomologicalGenusH0KX`).

These complete the genus-identification chain
`analyticGenus ℂ X = h⁰(X, K_X) = h¹(X, 𝒪_X) = RSGenus X` started
in `GenusIdentification.lean`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Sorry-free.** `RSGenus X = h⁰(X, K_X)` on a compact connected
Riemann surface. Composes the analytic-vs-cohomological-via-𝒪_X
identity (`RSGenus_eq_analyticGenus`) with the analytic-vs-
cohomological-via-K_X identity
(`analyticGenus_eq_cohomological_genus_h0_KX`). -/
theorem RSGenus_eq_h0_KX
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)] :
    RSGenus X = cohomologicalGenusH0KX X := by
  rw [RSGenus_eq_analyticGenus X, analyticGenus_eq_cohomological_genus_h0_KX X]

/-- **Sorry-free corollary.** Unfolded form of `RSGenus_eq_h0_KX`:
`RSGenus X` equals the `finrank` of `H⁰(X, K_X)` directly. -/
theorem RSGenus_eq_finrank_h0_KX
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)] :
    RSGenus X
      = Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0) := by
  rw [RSGenus_eq_h0_KX X]
  rfl

end JacobianChallenge.HolomorphicForms
