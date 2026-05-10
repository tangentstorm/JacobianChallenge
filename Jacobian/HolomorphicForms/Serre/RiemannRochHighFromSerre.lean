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
  `deg (L⁻¹ ⊗ K_X) = 2g − 2 − deg L` — **discharged** (sorry-free
  assembly from three frontier sub-lemmas).
* `riemann_roch_high_degree_via_serre` — the Serre-duality
  reduction itself (frontier).

## Sub-obligations for the degree formula

The degree formula `deg(L⁻¹ ⊗ K_X) = 2g − 2 − deg L` is decomposed
into three elementary line-bundle-degree identities:

1. `RSLineBundleDegree_tensor` — additivity of degree under tensor:
   `deg(F ⊗ G) = deg F + deg G`.
2. `RSLineBundleDegree_dual` — degree of the inverse:
   `deg(L⁻¹) = −deg L`.
3. `RSLineBundleDegree_canonical` — degree of the canonical bundle:
   `deg(K_X) = 2g − 2`.

Each is a named frontier sorry that isolates a single classical fact
about line-bundle degrees on compact Riemann surfaces. Once the
`RSLineBundleDegree` API is grounded (divisor correspondence +
Chern class), all three become straightforward.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-! ### Frontier sub-lemmas for the degree formula -/

/-- **Frontier theorem (sorry).** Additivity of line-bundle degree
under tensor product: `deg(F ⊗ G) = deg F + deg G`.

Classically immediate from the divisor correspondence
(`div(F ⊗ G) = div F + div G`) or the first Chern class
(`c₁(F ⊗ G) = c₁(F) + c₁(G)`). -/
theorem RSLineBundleDegree_tensor
    (X : Type*) [TopologicalSpace X]
    (F G : RSLineBundleSheaf X) :
    RSLineBundleDegree X (RSTensorAbSheaf X F G)
      = RSLineBundleDegree X F + RSLineBundleDegree X G := by
  sorry

/-- **Frontier theorem (sorry).** Degree of the dual (inverse) line
bundle: `deg(L⁻¹) = −deg L`.

Classically immediate from `L ⊗ L⁻¹ ≅ 𝒪_X` and `deg 𝒪_X = 0`,
combined with additivity. -/
theorem RSLineBundleDegree_dual
    (X : Type*) [TopologicalSpace X]
    (L : RSLineBundleSheaf X) :
    RSLineBundleDegree X (RSLineBundleDual X L)
      = -RSLineBundleDegree X L := by
  sorry

/-- **Frontier theorem (sorry).** Degree of the canonical
(dualizing) line bundle on a compact Riemann surface:
`deg(K_X) = 2g − 2`.

This is a restatement of `canonical_degree_eq_two_genus_minus_two`
from `CanonicalDivisor.lean` without the `ConnectedSpace` and
sheaf-cohomology module instance hypotheses; those are artifacts of
the Euler-characteristic proof route and are not needed for the
bare degree statement. -/
theorem RSLineBundleDegree_canonical
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    RSLineBundleDegree X (RSDualizingSheaf X)
      = 2 * (RSGenus X : ℤ) - 2 := by
  sorry

/-! ### Discharged degree formula -/

/-- **Discharged (sorry-free assembly).** Degree of the line-bundle
expression `L⁻¹ ⊗ K_X` equals `2g − 2 − deg L`.

Assembled from:
- `RSLineBundleDegree_tensor` (additivity under ⊗),
- `RSLineBundleDegree_dual` (degree of inverse),
- `RSLineBundleDegree_canonical` (degree of K_X = 2g−2).

The proof is sorry-free; the analytic content is isolated in the
three sub-lemmas above. -/
theorem RSLineBundleDegree_dual_tensor_canonical
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (L : RSLineBundleSheaf X) :
    RSLineBundleDegree X
        (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X))
      = 2 * (RSGenus X : ℤ) - 2 - RSLineBundleDegree X L := by
  rw [RSLineBundleDegree_tensor, RSLineBundleDegree_dual,
      RSLineBundleDegree_canonical]
  ring

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
