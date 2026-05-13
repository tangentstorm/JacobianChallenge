import Jacobian.HolomorphicForms.EulerCharLineBundle
import Jacobian.HolomorphicForms.Serre.H0CanonicalIdentification
import Jacobian.HolomorphicForms.H1DualizingSheaf
import Mathlib.Tactic.Linarith
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Canonical divisor degree on a compact Riemann surface

Frontier statement of the classical degree-of-the-canonical-divisor
formula

  deg(K_X) = 2g − 2

on a compact Riemann surface `X` of genus `g`. This is the
parameter-free corollary of Riemann-Roch obtained by specialising
`thm:euler-char-line-bundle` to `L = K_X` and using Serre duality
to identify `H¹(K_X) ≃ ℂ`, hence `χ(K_X) = g − 1`, hence
`deg(K_X) + 1 − g = g − 1`.

This file is the natural sec02 follow-up to the merged
`SheafCohomologyRS.lean` / `SerreDualityRS.lean` /
`EulerCharLineBundle.lean` chain: every analytic-frontier
prerequisite already lives in those files as a frontier sorry or a
frontier class, so the only new content here is the formula
`deg K_X = 2g − 2` and the project-side packaging.

## What this file provides

* `RSCanonicalDegree X : ℤ` — concrete `def` (no sorry):
  `RSLineBundleDegree X (RSDualizingSheaf X)`. Inherits the upstream
  frontier-`sorry` on `RSLineBundleDegree` / `RSDualizingSheaf`, but
  the derived definition itself is sorry-free.
* `canonical_degree_eq_two_genus_minus_two X` — frontier theorem
  (sorry) asserting `deg(K_X) = 2g − 2`. The proof outline (RR for
  L = K_X plus Serre duality) is named in the docstring.

## What this file does NOT provide

* the explicit Mathlib discharge of either ingredient — both
  ingredients are themselves frontier sorries above (in
  `RSLineBundleDegree` and `RSGenus`),
* the formal sheaf-cohomology computation `H¹(K_X) ≃ ℂ` (depends on
  Serre duality + `H⁰(𝒪_X) ≃ ℂ`, both ABSENT in v4.28.0).

These belong to follow-up nodes once the analytic-sheaf machinery
lands (`H⁰(𝒪_X) = ℂ` for compact connected RS via maximum modulus
principle; `H¹(K_X) ≃ ℂ` via Serre).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- The degree of the canonical divisor `K_X` on a compact Riemann
surface, packaged via the project-side `RSDualizingSheaf` and
`RSLineBundleDegree` API.

Concrete (no sorry); the upstream frontier-`sorry` on
`RSLineBundleDegree` and `RSDualizingSheaf` propagates through, but
this derived definition itself does not introduce any new sorry.

The explicit universe annotation `.{_, 0}` pins the
`AddCommGrpCat`-universe parameter to match the convention used by
`RSSheafCohomology` and friends in `SheafCohomologyRS.lean`. -/
noncomputable def RSCanonicalDegree
    (X : Type*) [TopologicalSpace X] : ℤ :=
  RSLineBundleDegree.{_, 0} X (RSDualizingSheaf X)

/-- **Frontier sheaf-cohomology computation.** The space of global
sections of the canonical sheaf has dimension `g`.

Bottom-up content: identify `H⁰(X, K_X)` with the project
`HolomorphicOneForm ℂ X` carrier defining `RSGenus X`. This is the
canonical sheaf/global holomorphic 1-form comparison. -/
theorem canonical_h0_finrank_eq_genus
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)] :
    Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0) = RSGenus X := by
  rw [LinearEquiv.finrank_eq (h0Canonical_isoHolomorphicOneForm X)]
  rfl

/-- **Frontier sheaf-cohomology computation.** The first cohomology of
the canonical sheaf has dimension `1`.

Bottom-up content: Serre duality identifies `H¹(X, K_X)` with the dual
of `H⁰(X, 𝒪_X)`, and compact connected Riemann surfaces have only
constant holomorphic functions, so `dim H⁰(X, 𝒪_X)=1`. -/
theorem canonical_h1_finrank_eq_one
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Module.finrank ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1) = 1 := by
  exact h1_dualizing_sheaf_one_dim X

/-- **Frontier sheaf-cohomology computation.** The Euler characteristic
of the canonical sheaf is `g - 1`.

Bottom-up content: `h⁰(K_X) = g` by the holomorphic-one-form definition
of genus, and `h¹(K_X) = 1` by Serre duality against the structure sheaf
plus the compact-connected maximum-principle computation
`H⁰(𝒪_X) ≃ ℂ`. -/
theorem canonical_eulerCharacteristic_eq_genus_minus_one
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSEulerCharacteristic X (RSDualizingSheaf X) = (RSGenus X : ℤ) - 1 := by
  have h0 := canonical_h0_finrank_eq_genus X
  have h1 := canonical_h1_finrank_eq_one X
  unfold RSEulerCharacteristic
  rw [h0, h1]
  norm_num

/-- **Frontier theorem (sorry).** Degree of the canonical divisor on
a compact Riemann surface of genus `g`:

  deg(K_X) = 2g − 2.

PROOF SKETCH (sorry pending the analytic frontier):
1. Apply `euler_char_line_bundle` to `L = RSDualizingSheaf X` to get

     χ(K_X) = deg(K_X) + 1 − g.

2. Compute `χ(K_X) = h⁰(K_X) − h¹(K_X) = g − 1`:
   * `h⁰(K_X) = g` by definition of the genus
     (`g := dim_ℂ H⁰(X, K_X)` is the holomorphic 1-form definition,
     equivalent to `dim_ℂ H¹(X, 𝒪_X)` via Serre duality);
   * `h¹(K_X) = 1` by Serre duality `H¹(K_X)* ≃ H⁰(𝒪_X) ≃ ℂ`,
     plus `dim_ℂ H⁰(𝒪_X) = 1` for compact connected `X`.
3. Combine: `g − 1 = deg(K_X) + 1 − g`, hence
   `deg(K_X) = 2g − 2`.

The proof is `sorry` because every step references analytic-sheaf
machinery (`RSGenus`, `RSGenus = h⁰(K_X)`, `H¹(K_X) ≃ ℂ`,
`H⁰(𝒪_X) ≃ ℂ`) that is ABSENT in Mathlib v4.28.0.

The hypothesis `[Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) q)]`
arguments are required by `euler_char_line_bundle`; they are not
auto-derivable from `Sheaf.H`'s `AddCommGroup`-only structure. -/
theorem canonical_degree_eq_two_genus_minus_two
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSCanonicalDegree X = 2 * (RSGenus X : ℤ) - 2 := by
  have hχK := canonical_eulerCharacteristic_eq_genus_minus_one X
  have hRR :
      RSEulerCharacteristic X (RSDualizingSheaf X) =
        RSLineBundleDegree X (RSDualizingSheaf X) + 1 - (RSGenus X : ℤ) :=
    euler_char_line_bundle X (RSDualizingSheaf X)
  unfold RSCanonicalDegree
  rw [hχK] at hRR
  linarith

end JacobianChallenge.HolomorphicForms
