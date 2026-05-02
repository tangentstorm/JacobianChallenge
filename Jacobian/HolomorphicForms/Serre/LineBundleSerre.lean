import Jacobian.HolomorphicForms.Serre.LineBundleDual
import Jacobian.HolomorphicForms.Serre.DatumExists

/-!
# Serre duality specialised to line bundles (frontier)

Round 16: a specialisation of the abstract Serre-duality datum to the
case of a line-bundle sheaf. Classically:

  H¹(X, L) ≃ H⁰(X, L⁻¹ ⊗ K_X)*    as ℂ-vector spaces.

This file states the existence form of that specialisation and
delegates to (a) the abstract Serre datum
(`serre_datum_for_canonical_dual_exists`) and (b) the line-bundle
identification of the canonical dual
(`serreDualSheaf_lineBundle_iso`).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** Existence of a Serre-duality datum
for a line bundle `L`, against the explicit dual `L⁻¹ ⊗ K_X`.

Decomposes into

* `serre_datum_for_canonical_dual_exists` (the abstract datum on the
  canonical dual `Hom(L, K_X)`), and
* `serreDualSheaf_lineBundle_iso` (the iso
  `Hom(L, K_X) ≃ L⁻¹ ⊗ K_X`).

Both are frontier; the two together replace the abstract round-2
existence on the canonical dual when the consumer prefers the
classical line-bundle expression. -/
theorem serre_duality_lineBundle_exists
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X) :
    ∃ (_ : Module ℂ (RSSheafCohomology X L 0))
      (_ : Module ℂ
        (RSSheafCohomology X
          (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X)) 1)),
      Nonempty (SerreDualityRSDatum X L
        (RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X))) := by
  sorry

end JacobianChallenge.HolomorphicForms
