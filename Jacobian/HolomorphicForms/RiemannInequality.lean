import Jacobian.HolomorphicForms.EulerCharLineBundle

/-!
# Riemann's inequality

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The "weaker half" of Riemann-Roch on a compact connected Riemann
surface: for any line bundle `L`,

  dim_ℂ H⁰(X, L) ≥ deg(L) + 1 − g.

Riemann published this inequality (1857) before Roch identified the
correction term `h¹(L)`. The full Roch correction is `h⁰(L) − h¹(L)
= deg L + 1 − g`; *Riemann's inequality* drops the non-negative
`h¹(L)` term.

The body of this file is **sorry-free**: it follows immediately from
`euler_char_line_bundle` plus the trivial observation that
`finrank` of an `AddCommGroup` is a non-negative integer.

## What this file provides

* `riemann_inequality_h0` — sorry-free Riemann inequality
  `h⁰(L) ≥ deg L + 1 − g`.
* `riemann_inequality_h1` — sorry-free symmetric statement
  `h¹(L) ≥ g − 1 − deg L`. Useful for sec02 effectivity arguments
  in the low-degree régime.

These complete the "monotone" half of the Riemann-Roch chain.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Riemann's inequality (sorry-free).** For any line bundle `L`
on a compact connected Riemann surface, the dimension of global
sections is at least `deg L + 1 − g`.

Follows from `euler_char_line_bundle`
(`χ(L) = deg L + 1 − g`) plus `h¹(L) ≥ 0` (the latter being trivial
for a `Module.finrank` cast to `ℤ`). -/
theorem riemann_inequality_h0
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ)
      ≥ RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  have h_chi : RSEulerCharacteristic X L
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
    euler_char_line_bundle X L
  have h_h1_nn : (0 : ℤ) ≤ Module.finrank ℂ (RSSheafCohomology X L 1) :=
    Int.natCast_nonneg _
  have : (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ)
        - (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ)
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := h_chi
  linarith

/-- **Symmetric Riemann inequality (sorry-free).** Dual statement:
`h¹(L) ≥ g − 1 − deg L`. Follows from the same Euler-char identity
and `h⁰(L) ≥ 0`. -/
theorem riemann_inequality_h1
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ)
      ≥ (RSGenus X : ℤ) - 1 - RSLineBundleDegree X L := by
  have h_chi : RSEulerCharacteristic X L
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
    euler_char_line_bundle X L
  have h_h0_nn : (0 : ℤ) ≤ Module.finrank ℂ (RSSheafCohomology X L 0) :=
    Int.natCast_nonneg _
  have : (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ)
        - (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ)
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := h_chi
  linarith

end JacobianChallenge.HolomorphicForms
