import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.ResidueMap

/-!
# Identification `H¹(X, K_X) ≃ₗ[ℂ] ℂ` (refined)

Round 15 refinement: `h1Canonical_isoToC` is now assembled from the
residue map `residueMap` and its inverse `residueMap_inverse`,
together with the round-trip identities. The four pieces
(`residueMap`, `residueMap_inverse`, `residueMap_left_inv`,
`residueMap_right_inv`) are strictly smaller named obligations
than the round-5 single sorry.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Refined (round 15).** Canonical `ℂ`-linear isomorphism
`H¹(X, K_X) ≃ₗ[ℂ] ℂ` on a compact connected Riemann surface,
assembled from `residueMap` and `residueMap_inverse` with the
round-trip identities `residueMap_left_inv` /
`residueMap_right_inv`. -/
noncomputable def h1Canonical_isoToC
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 ≃ₗ[ℂ] ℂ where
  toFun     := residueMap X
  invFun    := residueMap_inverse X
  left_inv  := residueMap_left_inv X
  right_inv := residueMap_right_inv X
  map_add'  := (residueMap X).map_add
  map_smul' := (residueMap X).map_smul

end JacobianChallenge.HolomorphicForms
