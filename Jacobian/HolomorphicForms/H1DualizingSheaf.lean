import Jacobian.HolomorphicForms.SerreDualityRS
import Jacobian.HolomorphicForms.HolomorphicCompactConstant
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `H¹(X, K_X) ≃ ℂ` on a compact Riemann surface

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The first cohomology of the dualizing sheaf on a compact connected
Riemann surface is one-dimensional over `ℂ`:

  dim_ℂ H¹(X, K_X) = 1.

This is the second of the two follow-up nodes flagged in
`Jacobian/HolomorphicForms/CanonicalDivisor.lean`'s docstring
(the first — `H⁰(𝒪_X) ≃ ℂ` — landed as
`Jacobian/HolomorphicForms/HolomorphicCompactConstant.lean`).

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` and `ref/scope-out.md`, the
ingredients are ABSENT:

* analytic structure sheaf `𝒪_X`,
* dualizing sheaf realisation,
* Serre duality nondegeneracy as an explicit dimension
  identification.

Hence the statement is provided as a sec02 frontier theorem with a
sorry proof; the proof outline (Serre duality `H¹(K_X) ≃ H⁰(𝒪_X)*`
plus `H⁰(𝒪_X) ≃ ℂ`) is named in the docstring.

## What this file provides

* `h1_dualizing_sheaf_one_dim X` — frontier theorem (sorry) asserting
  `finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1) = 1`.
* `h1_dualizing_sheaf_finiteDimensional X` — sorry-free corollary
  (definitional via `finrank` machinery): the cohomology is finite-
  dimensional, with explicit `finrank` value `1`.

## What this file does NOT provide

* an explicit Mathlib discharge of the dimension claim — depends on
  the missing Serre-duality nondegeneracy + `H⁰(𝒪_X) ≃ ℂ`,
* a categorical / sheaf-theoretic isomorphism — only the dimension
  count.

These belong to follow-up nodes once the analytic-sheaf machinery
lands.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** The first cohomology of the
dualizing sheaf on a compact connected Riemann surface is
one-dimensional over `ℂ`.

PROOF SKETCH (sorry pending the analytic frontier):

1. By Serre duality (`serre_duality_rs` applied to `F = 𝒪_X`),
   `H¹(X, K_X) ≃ H⁰(X, 𝒪_X)*` as `ℂ`-vector spaces.
2. By `holomorphic_compact_connected_constant`, every holomorphic
   function on a compact connected `X` is constant; hence
   `H⁰(X, 𝒪_X) ≃ ℂ` (one-dimensional).
3. The dual of a one-dimensional `ℂ`-vector space is one-dimensional;
   transporting through the Serre-duality iso gives
   `dim_ℂ H¹(K_X) = 1`.

The `[Module ℂ …]` instance argument is required because
`RSSheafCohomology` provides only an `AddCommGroup` structure;
Mathlib's `finrank` returns `0` on non-`ℂ`-module data, so the
statement is vacuous unless the consumer supplies the
`ℂ`-module structure. -/
theorem h1_dualizing_sheaf_one_dim
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1) = 1 := by
  sorry

/-- Finite-dimensionality corollary: `H¹(X, K_X)` is finite-
dimensional over `ℂ`, with `finrank` equal to `1`. Sorry-free given
`h1_dualizing_sheaf_one_dim`. -/
theorem h1_dualizing_sheaf_finiteDimensional
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1) ≠ 0 := by
  rw [h1_dualizing_sheaf_one_dim X]
  exact one_ne_zero

end JacobianChallenge.HolomorphicForms
