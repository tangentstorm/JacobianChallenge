import Jacobian.HolomorphicForms.RiemannRochHighDegree

/-!
# Strong Riemann-Roch in the high-degree régime

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

For a line bundle of degree `> 2g − 2` on a compact connected Riemann
surface, the dimension of global sections is determined exactly by
the degree and the genus:

  dim_ℂ H⁰(X, L) = deg(L) + 1 − g.

This is the workhorse formula behind classical statements such as
"every divisor class of degree `≥ 2g − 1` is effective" and the
Abel-Jacobi point-separation argument.

The body of this file combines two upstream theorems:

* `riemann_roch_high_degree_h0` (sorry-free corollary of the
  high-degree Serre vanishing) — in the high-degree régime,
  `χ(X, L) = dim_ℂ H⁰(X, L)`.
* `euler_char_line_bundle` (frontier sorry) —
  `χ(X, L) = deg L + 1 − g`.

The combined theorem is therefore **sorry-free in this file**; the
deep content lives in the two upstream frontier sorries
(`riemann_roch_high_degree` via `riemann_roch_low_degree`/Serre
duality, and `euler_char_line_bundle`). -/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Strong Riemann-Roch (sorry-free).** For a line bundle `L` of
degree `> 2g − 2` on a compact connected Riemann surface,
`dim_ℂ H⁰(X, L) = deg(L) + 1 − g`.

Combines `riemann_roch_high_degree_h0`
(`χ(X, L) = h⁰(L)` in the high-degree régime) with
`euler_char_line_bundle` (`χ(X, L) = deg L + 1 − g`). -/
theorem riemann_roch_strong_h0
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)]
    (h_high : RSLineBundleDegree X L > 2 * (RSGenus X : ℤ) - 2) :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ)
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  rw [← riemann_roch_high_degree_h0 X L h_high, euler_char_line_bundle X L]

/-- **Effectivity corollary (sorry-free).** When `deg L ≥ 2g`, the
strong Riemann-Roch formula gives `h⁰(L) ≥ g + 1 ≥ 1` — in particular
`L` admits at least one nonzero global section.

The bound `deg L ≥ 2g` is the standard "Bertini-flavoured" lower
bound that works uniformly across all genera, including `g = 0`. -/
theorem riemann_roch_strong_h0_pos
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)]
    (h_deg : RSLineBundleDegree X L ≥ 2 * (RSGenus X : ℤ)) :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) ≥ 1 := by
  have h_high : RSLineBundleDegree X L > 2 * (RSGenus X : ℤ) - 2 := by linarith
  have h_eq := riemann_roch_strong_h0 X L h_high
  have hg : (0 : ℤ) ≤ (RSGenus X : ℤ) := Int.natCast_nonneg _
  linarith

end JacobianChallenge.HolomorphicForms
