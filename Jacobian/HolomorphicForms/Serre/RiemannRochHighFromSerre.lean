import Jacobian.HolomorphicForms.Serre.LineBundleSerre
import Jacobian.HolomorphicForms.EulerCharLineBundle

/-!
# Serre vanishing in the high-degree régime (refinement)

Round 18: refine `riemann_roch_high_degree` (Serre vanishing) by
exposing the named obligation that links it to Serre duality + the
low-degree vanishing.

Classically: `H¹(L) ≃ H⁰(K_X − L)*` via Serre duality. If
`deg L > 2g − 2` then `deg (K_X − L) = 2g − 2 − deg L < 0`, so
`H⁰(K_X − L) = 0` (low-degree vanishing), hence `H¹(L) = 0`.

The named obligations exposed here are:

* `RSLineBundleDegree_dual_tensor_canonical` — the degree formula
  `deg (L⁻¹ ⊗ K_X) = 2g − 2 − deg L` (frontier).
* `riemann_roch_high_degree_via_serre` — the Serre-duality
  reduction itself (frontier).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** Degree of the line-bundle expression
`L⁻¹ ⊗ K_X` equals `2g − 2 − deg L`.

Will be discharged once `RSLineBundleDegree`, `RSLineBundleDual`,
`RSTensorAbSheaf`, and `RSGenus` are jointly grounded out (a
mid-tier obligation in the line-bundle API). -/
theorem RSLineBundleDegree_dual_tensor_canonical
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (L : RSLineBundleSheaf X) :
    RSLineBundleDegree X
        (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X))
      = 2 * (RSGenus X : ℤ) - 2 - RSLineBundleDegree X L := by
  sorry

/-- **Frontier theorem (sorry).** The Serre-duality reduction:
finite-rank `H¹(X, L)` equals finite-rank `H⁰(X, L⁻¹ ⊗ K_X)`.

Once dischargeable from `serre_duality_lineBundle_exists` plus the
fact that the dual of a finite-dim vector space has the same rank,
this reduces `riemann_roch_high_degree` to
`riemann_roch_low_degree X (L⁻¹ ⊗ K_X) ...`. -/
theorem riemann_roch_high_degree_via_serre
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 1)]
    [Module ℂ (RSSheafCohomology X
      (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X)) 0)] :
    Module.finrank ℂ (RSSheafCohomology X L 1) =
      Module.finrank ℂ (RSSheafCohomology X
        (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X)) 0) := by
  sorry

end JacobianChallenge.HolomorphicForms
