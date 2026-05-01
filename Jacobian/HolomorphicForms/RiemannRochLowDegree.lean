import Jacobian.HolomorphicForms.EulerCharLineBundle

/-!
# Vanishing of `H⁰(X, L)` for negative-degree line bundles

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A line bundle of negative degree on a compact connected Riemann
surface has no nonzero global sections:

  deg(L) < 0 ⇒ dim_ℂ H⁰(X, L) = 0.

This is a sec02 MEDIUM corollary of the divisor theory of holomorphic
sections on a compact Riemann surface: any nonzero global section
`s : L` would have an *effective* zero divisor `(s) ≥ 0` of total
degree `deg L`, contradicting `deg L < 0`.

The result is the symmetric companion (under Serre duality) of the
Serre vanishing theorem for high-degree line bundles
(`deg L > 2g − 2 ⇒ h¹(L) = 0`), which would be the natural
follow-up node.

## What this file provides

* `riemann_roch_low_degree` — frontier theorem (sorry) asserting
  `finrank ℂ (RSSheafCohomology X L 0) = 0` whenever
  `RSLineBundleDegree X L < 0`.
* `riemann_roch_low_degree_eulerChar` — sorry-free corollary:
  combined with `euler_char_line_bundle`, the Euler characteristic
  reduces to `χ(X, L) = − dim_ℂ H¹(X, L)` in the negative-degree
  régime.

## What this file does NOT provide

* the analytic discharge of the vanishing — depends on the
  divisor↔line-bundle correspondence and divisor degree theory,
  ABSENT in Mathlib v4.28.0,
* the corresponding Serre vanishing for `H¹` (high-degree régime),
* finite-dimensionality of `H⁰(X, L)` itself (a frontier-class
  typeclass argument upstream).

These belong to follow-up nodes once the analytic-sheaf machinery
lands.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** A line bundle of strictly negative
degree on a compact connected Riemann surface has no nonzero global
sections.

PROOF SKETCH (sorry pending the analytic frontier): a nonzero global
section `s ∈ H⁰(X, L)` defines an effective zero divisor `(s) ≥ 0`
on `X`; the degree of `(s)` equals `RSLineBundleDegree X L` (the
divisor-line-bundle correspondence); but `deg (s) ≥ 0` for an
effective divisor, so `RSLineBundleDegree X L ≥ 0`, contradicting
`h_neg`. Hence `H⁰(X, L) = 0`. -/
theorem riemann_roch_low_degree
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    (_h_neg : RSLineBundleDegree X L < 0) :
    Module.finrank ℂ (RSSheafCohomology X L 0) = 0 := by
  sorry

/-- **Corollary (sorry-free).** Combined with the Euler-characteristic
identity `χ(X, L) = deg L + 1 − g`, the negative-degree vanishing
gives `χ(X, L) = − dim_ℂ H¹(X, L)`, i.e. the Euler characteristic is
controlled entirely by `H¹`. Useful as an intermediate step toward
Serre vanishing in the high-degree régime via duality. -/
theorem riemann_roch_low_degree_eulerChar
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)]
    (h_neg : RSLineBundleDegree X L < 0) :
    RSEulerCharacteristic X L
      = - (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) := by
  unfold RSEulerCharacteristic
  rw [riemann_roch_low_degree X L h_neg]
  simp

end JacobianChallenge.HolomorphicForms
