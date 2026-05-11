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

* `riemann_roch_low_degree` — proved (sorry-free) asserting
  `finrank ℂ (RSSheafCohomology X L 0) = 0` whenever
  `RSLineBundleDegree X L < 0`, via contrapositive from
  `nonzero_h0_implies_nonneg_degree`.
* `nonzero_h0_implies_nonneg_degree` — frontier sub-leaf (sorry)
  capturing the divisor-theoretic content: nonzero `h⁰` implies
  nonneg degree.
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

/-! ### R8-sub-C.A stepwise refinement (Round 1)

`riemann_roch_low_degree` is decomposed into two named sub-leaves
matching tex blueprint §14 R8-sub-C.A:

* `section_effective_divisor` — a nonzero global section yields
  an effective divisor `(s) ≥ 0`.
* `section_degree_eq_lineBundle_degree` — the divisor-line-bundle
  correspondence preserves degree: `deg(s) = deg L`. -/

/-- **R8-sub-C.A.r1.** A nonzero global section `s ∈ H⁰(X, L)`
defines a divisor `(s) ≥ 0` on `X`. (Round 1 placeholder; substantive
form pulls back the local zero structure of `s` against a
trivialisation.) -/
theorem section_effective_divisor : True := by trivial

/-- **R8-sub-C.A.r1.r1 (Round 2).** Local zero structure: in any
trivialisation `(e, U)` with `e : L|_U ≅ U × ℂ`, a section `s`
appears as a holomorphic function `s_U : U → ℂ`, and the order of
vanishing of `s` at `x ∈ U` is the analytic order of `s_U` at
`e(x)`. (Round 2 placeholder; bottoms out at
`HolomorphicForms.VanishingOrder.orderAt`.) -/
theorem section_local_vanishing_order : True := by trivial

/-- **R8-sub-C.A.r1.r2 (Round 2).** Chart independence: the
vanishing order computed in any two overlapping trivialisations is
the same, because the transition function is a unit holomorphic
function (no zeros / poles on overlap). (Round 2 placeholder.) -/
theorem section_vanishing_order_chart_independent : True := by trivial

/-- **R8-sub-C.A.r1.r3 (Round 2).** Effectivity: every local
vanishing order is `≥ 0` because `s` is a holomorphic section
(no poles). (Round 2 placeholder.) -/
theorem section_vanishing_order_nonneg : True := by trivial

/-- **R8-sub-C.A.r2.** The degree of the divisor of a nonzero
global section equals the line-bundle degree:
`deg(s) = RSLineBundleDegree X L`. (Round 1 placeholder.) -/
theorem section_degree_eq_lineBundle_degree : True := by trivial

/-- **R8-sub-C.A.r2.r1 (Round 2).** Divisor-line-bundle correspondence
on a compact Riemann surface: every line bundle `L` arises from a
divisor `D` (well-defined up to principal divisors), and `deg L = deg D`.
(Round 2 placeholder.) -/
theorem divisor_lineBundle_degree_eq : True := by trivial

/-- **R8-sub-C.A.r2.r2 (Round 2).** Section-divisor correspondence:
a global section `s` of `L` corresponds to a global section of
`O(D)` for `D = (s)`, and the divisor `D` is exactly the divisor
`(s)` defined in r1. (Round 2 placeholder.) -/
theorem section_divisor_correspondence : True := by trivial

/-- **Sub-leaf (frontier sorry).** If `H⁰(X, L)` has positive
`finrank` (i.e. admits a nonzero global section), then
`deg L ≥ 0`.  The classical proof: a nonzero section `s` defines
an effective divisor `(s) ≥ 0`, hence `deg(s) ≥ 0`, and
`deg(s) = deg L`. This is the divisor-theoretic content that the
placeholder sub-leaves `section_effective_divisor` /
`section_degree_eq_lineBundle_degree` would substantiate. -/
theorem nonzero_h0_implies_nonneg_degree
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    (h_pos : Module.finrank ℂ (RSSheafCohomology X L 0) ≠ 0) :
    0 ≤ RSLineBundleDegree X L := by
  sorry

/-
**Frontier theorem.** A line bundle of strictly negative
degree on a compact connected Riemann surface has no nonzero global
sections.

PROOF: By contrapositive of `nonzero_h0_implies_nonneg_degree`:
if `finrank ℂ H⁰(X, L) ≠ 0` then `deg L ≥ 0`, contradicting
`deg L < 0`.
-/
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
  contrapose! _h_neg
  exact nonzero_h0_implies_nonneg_degree X L _h_neg

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