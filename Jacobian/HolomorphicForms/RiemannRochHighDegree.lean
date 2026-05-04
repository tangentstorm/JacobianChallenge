import Jacobian.HolomorphicForms.RiemannRochLowDegree
import Jacobian.HolomorphicForms.SerreDualityRS
import Jacobian.HolomorphicForms.Serre.RiemannRochHighFromSerre
import Mathlib.Tactic.Linarith

/-!
# Vanishing of `H¹(X, L)` for high-degree line bundles (Serre vanishing)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A line bundle of degree strictly greater than `2g − 2` on a compact
connected Riemann surface has vanishing first cohomology:

  deg(L) > 2g − 2 ⇒ dim_ℂ H¹(X, L) = 0.

This is the Serre vanishing theorem in dimension 1: the symmetric
companion (under Serre duality `H¹(L) ≃ H⁰(K_X − L)*`) of
`riemann_roch_low_degree` (`deg L < 0 ⇒ h⁰(L) = 0`). Together with
the Euler-characteristic identity
`χ(X, L) = deg L + 1 − g`, it gives the **strong Riemann-Roch**
calculation

  dim_ℂ H⁰(X, L) = deg L + 1 − g

in the high-degree régime — the workhorse formula behind
`thm:abel-existence` and the embedding theorems.

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 the analytic-frontier
ingredients are ABSENT. The proof plan is itself a chain of frontier
sorries: we record the statement so downstream consumers can quote it
parametrically.

## What this file provides

* `riemann_roch_high_degree` — frontier theorem (sorry) asserting
  `finrank ℂ (RSSheafCohomology X L 1) = 0` whenever
  `RSLineBundleDegree X L > 2 * RSGenus X − 2`.
* `riemann_roch_high_degree_h0` — sorry-free corollary in the
  high-degree régime: `χ(X, L) = dim_ℂ H⁰(X, L)`, i.e. the Euler
  characteristic equals `h⁰(L)`. Combined with
  `euler_char_line_bundle` this gives the strong Riemann-Roch
  formula `h⁰(L) = deg L + 1 − g`.

## What this file does NOT provide

* the analytic discharge of the vanishing — depends on Serre duality
  (`serre_duality_rs`, frontier sorry) and the line-bundle subtraction
  `K_X − L` (ABSENT analytic-sheaf machinery),
* the strong Riemann-Roch formula stated as its own theorem (it is
  immediate from `riemann_roch_high_degree_h0` +
  `euler_char_line_bundle`; left to the consumer).

These belong to follow-up nodes once the analytic-sheaf machinery
lands.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** A line bundle of strictly more than
`2g − 2` degree on a compact connected Riemann surface has vanishing
first cohomology — Serre vanishing in dimension 1.

PROOF SKETCH (sorry pending the analytic frontier): apply Serre
duality (`serre_duality_rs`) to identify
`H¹(X, L) ≃ H⁰(X, K_X − L)*` as `ℂ`-vector spaces; the line bundle
`K_X − L` has degree `2g − 2 − deg L < 0` by `h_high`, so by
`riemann_roch_low_degree X (K_X − L) (by linarith)` the dual space
`H⁰(X, K_X − L)` is zero-dimensional; the dual of a zero-dimensional
space is zero-dimensional; hence `H¹(X, L)` is zero-dimensional. -/
theorem riemann_roch_high_degree
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 1)]
    (h_high : RSLineBundleDegree X L > 2 * (RSGenus X : ℤ) - 2) :
    Module.finrank ℂ (RSSheafCohomology X L 1) = 0 := by
  let Ldual : RSLineBundleSheaf X :=
    RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X)
  letI : Module ℂ (RSSheafCohomology X Ldual 0) :=
    serreDualSheaf_module_H0 X Ldual
  have hdeg :
      RSLineBundleDegree X Ldual =
        2 * (RSGenus X : ℤ) - 2 - RSLineBundleDegree X L := by
    simpa [Ldual] using RSLineBundleDegree_dual_tensor_canonical X L
  have hneg : RSLineBundleDegree X Ldual < 0 := by
    rw [hdeg]
    linarith
  rw [riemann_roch_high_degree_via_serre X L]
  simpa [Ldual] using riemann_roch_low_degree X Ldual hneg

/-- **Corollary (sorry-free).** In the high-degree régime
`deg L > 2g − 2`, the Euler characteristic equals `h⁰(L)`. Combined
with `euler_char_line_bundle` this gives the strong Riemann-Roch
formula `h⁰(L) = deg L + 1 − g`. -/
theorem riemann_roch_high_degree_h0
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)]
    (h_high : RSLineBundleDegree X L > 2 * (RSGenus X : ℤ) - 2) :
    RSEulerCharacteristic X L
      = (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) := by
  unfold RSEulerCharacteristic
  rw [riemann_roch_high_degree X L h_high]
  simp

end JacobianChallenge.HolomorphicForms
