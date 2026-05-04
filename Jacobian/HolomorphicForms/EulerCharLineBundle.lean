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

/-! ### TOPDOWN decomposition (round 1)

The headline `euler_char_line_bundle` (Riemann-Roch in Euler-
characteristic form, `χ(X, L) = deg L + 1 - g`) is split into 4 named
sub-obligations + a sorry-free assembly. The decomposition isolates
the two classical-analysis halves of Riemann-Roch — the Riemann
inequality (lower bound, Mittag-Leffler / global section construction)
and the Serre-duality half (upper bound, dual cohomology vanishing) —
plus a structural unfolding leaf and a squeeze-equality leaf. Two of
the leaves are sorry-free; the genuine analytic content is concentrated
in the two bound sub-leaves.

The shape mirrors the classical proof: the inequality `h⁰ - h¹ ≥ deg + 1 - g`
goes back to Riemann (1857); the matching `h⁰ - h¹ ≤ deg + 1 - g`
follows from Serre duality applied to `L⁻¹ ⊗ K_X`. Squeezing them
together gives Riemann-Roch as an equality (Roch, 1865). -/

/-- **Sub-leaf 1 (Riemann's inequality, `≥` direction).** The integer
difference `(h⁰(L) : ℤ) - (h¹(L) : ℤ)` is at least `deg L + 1 - g`.

Bottom-up content: the classical Riemann inequality
(`Jacobian/HolomorphicForms/RiemannInequality.lean`); equivalent to
the existence of "many" global sections of any high-degree line
bundle (Mittag-Leffler). Frontier-bound on the divisor-line-bundle
correspondence + finite-dimensional cohomology. -/
theorem h0_minus_h1_ge_riemann
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) ≥
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  sorry

/-- **Sub-leaf 2 (Serre-duality direction, `≤`).** The integer
difference `(h⁰(L) : ℤ) - (h¹(L) : ℤ)` is at most `deg L + 1 - g`.

Bottom-up content: apply Riemann's inequality to the dual line bundle
`L⁻¹ ⊗ K_X` (whose degree is `2g - 2 - deg L`), then trade
`h⁰(L⁻¹ ⊗ K_X) = h¹(L)` and `h¹(L⁻¹ ⊗ K_X) = h⁰(L)` via Serre
duality. Frontier-bound on the canonical bundle, the line-bundle
duality + tensor product, and Serre duality
(`Jacobian/HolomorphicForms/SerreDualityRS.lean`). -/
theorem h0_minus_h1_le_riemann
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) ≤
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  sorry

/-- **Sub-leaf 3 (sorry-free squeeze).** Combining the lower and upper
bounds gives the headline equality on the integer-difference form
`h⁰ - h¹`.  Pure `Int.le_antisymm`, no analytic content. -/
theorem h0_minus_h1_eq_riemann_roch
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) =
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
  le_antisymm (h0_minus_h1_le_riemann X L) (h0_minus_h1_ge_riemann X L)

/-- **Sub-leaf 4 (sorry-free unfolding).** The Euler characteristic
unfolds definitionally to the integer difference of finranks. -/
theorem rsEulerCharacteristic_eq_h0_minus_h1
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    RSEulerCharacteristic X L =
      (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) := rfl

/-- **Headline theorem (sorry-free assembly).** Riemann-Roch for line
bundles on a compact Riemann surface, in Euler-characteristic form:

  χ(X, L) = deg(L) + 1 - g.

Assembled from the four sub-leaves above:
- (4) `rsEulerCharacteristic_eq_h0_minus_h1`: rewrite χ as h⁰ - h¹;
- (3) `h0_minus_h1_eq_riemann_roch`: rewrite h⁰ - h¹ as deg + 1 - g
  (itself a sorry-free `Int.le_antisymm` of (1) and (2)).

The genuine analytic obligations are isolated in sub-leaves (1)
[Riemann inequality] and (2) [Serre duality], each individually
attackable. Once `RiemannInequality` lands, the squeeze argument
discharges the headline immediately. -/
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
  rw [rsEulerCharacteristic_eq_h0_minus_h1 X L]
  exact h0_minus_h1_eq_riemann_roch X L

end JacobianChallenge.HolomorphicForms
