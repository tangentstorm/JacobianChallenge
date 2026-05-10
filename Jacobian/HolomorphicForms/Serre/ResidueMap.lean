import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.HarmonicForms

/-!
# Residue / integration map for `H¹(X, K_X)` (frontier)

The classical realisation of `H¹(X, K_X) → ℂ` on a compact Riemann
surface is the **residue map** (Čech model) or the **integration map**
(Dolbeault model: ∫_X ω for the harmonic representative ω).

Round 15 names two pieces:

1. `residueMap X` — the linear map `H¹(X, K_X) → ℂ` itself
   (frontier);
2. `residueMap_isIso` — the fact that this map is a `ℂ`-linear
   isomorphism (frontier; equivalent to `dim H¹(K_X) = 1` plus
   nontrivial residue).

`h1Canonical_isoToC X` (round 5) is then the bundled form of
`residueMap` with its inverse, and gives `serreTraceMap` its concrete
content.

## Implementation note

The round-trip identities `residueMap_left_inv` /
`residueMap_right_inv` are discharged from a single sorry'd
`LinearEquiv` (`residueMapEquiv`), so the remaining sorry is
concentrated in one place while the algebraic round-trip properties
hold definitionally.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** The canonical `ℂ`-linear equivalence
`H¹(X, K_X) ≃ₗ[ℂ] ℂ` on a compact connected Riemann surface.
All frontier sorry is concentrated here; the forward map
(`residueMap`), inverse (`residueMap_inverse`), and round-trip
identities are derived from this equivalence. -/
noncomputable def residueMapEquiv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 ≃ₗ[ℂ] ℂ := by
  sorry

/-- **Frontier `def`.** Residue / integration map
`H¹(X, K_X) → ℂ` on a compact connected Riemann surface, extracted
as the forward direction of `residueMapEquiv`. -/
noncomputable def residueMap
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 →ₗ[ℂ] ℂ :=
  (residueMapEquiv X).toLinearMap

/-- **Frontier `def`.** Inverse of the residue / integration map,
extracted as the backward direction of `residueMapEquiv`. -/
noncomputable def residueMap_inverse
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    ℂ →ₗ[ℂ] RSSheafCohomology X (RSDualizingSheaf X) 1 :=
  (residueMapEquiv X).symm.toLinearMap

/-- **Proved.** Round-trip identity 1: `residueMap_inverse`
followed by `residueMap` is the identity on the domain. -/
theorem residueMap_left_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.LeftInverse (residueMap_inverse X) (residueMap X) :=
  (residueMapEquiv X).symm_apply_apply

/-- **Proved.** Round-trip identity 2: `residueMap`
followed by `residueMap_inverse` is the identity on `ℂ`. -/
theorem residueMap_right_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.RightInverse (residueMap_inverse X) (residueMap X) :=
  (residueMapEquiv X).apply_symm_apply

end JacobianChallenge.HolomorphicForms
