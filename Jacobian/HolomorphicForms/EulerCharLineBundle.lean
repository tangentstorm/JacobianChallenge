import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.SerreDualityRS
import Jacobian.HolomorphicForms.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Euler characteristic of a line bundle on a compact Riemann surface

Frontier statement of the Euler-characteristic-of-line-bundle
formula (a.k.a. Riemann-Roch in its bare form):

  χ(X, L) = deg(L) + 1 - g

where `χ(X, L) = dim_ℂ H⁰(X, L) - dim_ℂ H¹(X, L)`, `deg(L)` is the
degree of the line bundle, and `g` is the genus of `X`.

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 and `ref/scope-out.md`,
the four classical-input ingredients are ABSENT:

* analytic structure sheaf `𝒪_X` and locally-free `𝒪_X`-module
  presentations of holomorphic line bundles,
* divisor ↔ line-bundle correspondence on a Riemann surface,
* `deg(L)` for a line bundle,
* finite-dimensionality of `H^q` for a coherent sheaf on a compact
  RS — covered as the frontier class
  `FiniteDimensionalSheafCohomologyRS` in
  `SheafCohomologyRS.lean`, but no concrete instance witnesses
  exist yet.

We therefore expose:

* `RSLineBundleDegree X L : ℤ` — frontier `def` (sorry) for `deg L`.
* `RSGenus X : ℕ` — frontier `def` (sorry) for the genus
  classically `dim_ℂ H¹(X, 𝒪_X)`.
* `RSEulerCharacteristic X L : ℤ` — concrete `def`, computed as
  `finrank ℂ H⁰(X, L) - finrank ℂ H¹(X, L)` once the consumer
  supplies the `[Module ℂ …]` instance arguments. (No sorry.)
* `euler_char_line_bundle X L` — frontier theorem (sorry) asserting
  the Riemann-Roch identity.

## What this file does NOT provide

* explicit divisor-of-a-line-bundle map,
* the `FiniteDimensionalSheafCohomologyRS` discharge for arbitrary
  line bundles (requires GAGA / coherent-sheaf machinery),
* Serre duality identification `H¹(L)* ≃ H⁰(L⁻¹ ⊗ K_X)` (lives in
  `SerreDualityRS.lean` already as a frontier class).

These belong to follow-up nodes
(`input:riemann-roch`, `prop:genus-zero-degree-one-map`).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** The degree of a line-bundle sheaf on
a compact Riemann surface. Classically equal to the degree of any
divisor representing the line bundle, or equivalently
`deg(c₁(L)) ∈ H²(X, ℤ)`; both routes require analytic-sheaf or
de Rham machinery ABSENT in Mathlib v4.28.0. -/
noncomputable opaque RSLineBundleDegree
    (X : Type*) [TopologicalSpace X]
    (_L : RSLineBundleSheaf X) : ℤ

/-- The genus of a compact Riemann surface, defined as
`dim_ℂ H⁰(X, Ω¹_X) = Module.finrank ℂ (HolomorphicOneForm ℂ X)`.

Classically `g = dim_ℂ H¹(X, 𝒪_X) = dim_ℂ H⁰(X, Ω¹_X)` by Serre
duality / Hodge theory.  The `H⁰(X, Ω¹)` realisation avoids the
frontier sheaf-cohomology prerequisites (`HasSheafify`, `HasExt`,
`Module ℂ` on `H¹(X, 𝒪_X)`) and gives a concrete `ℕ` for every
complex-manifold charted space.  When the space of holomorphic
1-forms is not finite-dimensional, `Module.finrank` returns `0` by
Mathlib convention; for a compact Riemann surface this dimension is
always finite and equals the topological genus. -/
noncomputable def RSGenus
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm ℂ X)

/-- The Euler characteristic of a line-bundle sheaf on a compact
Riemann surface, computed as
`finrank ℂ H⁰(X, L) - finrank ℂ H¹(X, L) : ℤ`.

Concrete (no sorry); however it requires the consumer to supply
`[Module ℂ (RSSheafCohomology X L q)]` instances for `q = 0, 1`
since `Sheaf.H` only gives `AddCommGroup`. The result is sensible
on cohomologies that turn out to be finite-dimensional ℂ-vector
spaces (witnessed by `FiniteDimensionalSheafCohomologyRS`); on
infinite-dimensional ones `Module.finrank` returns `0`, which is
the harmless Mathlib convention. -/
noncomputable def RSEulerCharacteristic
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] : ℤ :=
  (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
    (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ)

/-- **Frontier theorem (sorry).** Riemann-Roch for line bundles on
a compact Riemann surface, in Euler-characteristic form:

  χ(X, L) = deg(L) + 1 - g.

The proof is `sorry` because every classical-input ingredient on
the right-hand side (`deg L`, `g`, finite-dimensionality of `H^0`
and `H^1`) is either a frontier sorry above, or a frontier-class
typeclass argument with no Mathlib v4.28.0 discharge. Once analytic
sheaves + divisor-line-bundle correspondence + Serre duality (cf.
`SerreDualityRS.lean`) all land, the discharge becomes a
self-contained piece of work whose dependencies are all named. -/
theorem euler_char_line_bundle
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    RSEulerCharacteristic X L =
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  sorry

end JacobianChallenge.HolomorphicForms
