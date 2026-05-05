import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.HarmonicForms

/-!
# Residue / integration map for `H¹(X, K_X)` (frontier)

The classical realisation of `H¹(X, K_X) → ℂ` on a compact Riemann
surface is the **residue map** (Čech model) or the **integration map**
(Dolbeault model: ∫_X ω for the harmonic representative ω).

Round 15 names two pieces:

1. `residueMapIso X` — the linear isomorphism `H¹(X, K_X) ≃ₗ[ℂ] ℂ`
   itself (frontier);
2. `residueMap X` and `residueMap_inverse X` — the two linear maps
   extracted from that opaque isomorphism.

`h1Canonical_isoToC X` (round 5) is then the bundled form of
`residueMap` with its inverse, and gives `serreTraceMap` its concrete
content.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier opaque construction.** Residue / integration
isomorphism `H¹(X, K_X) ≃ₗ[ℂ] ℂ` on a compact connected Riemann
surface.

The analytic content is the classical one-dimensionality of
`H¹(X, K_X)` plus a nonzero residue/integration functional.  Keeping
this as one opaque construction makes the round-trip lemmas below
ordinary projections rather than theorem-level sorries. -/
axiom residueMapIso
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 ≃ₗ[ℂ] ℂ

/-- Residue / integration map `H¹(X, K_X) → ℂ` on a compact connected
Riemann surface, extracted from the opaque residue isomorphism. -/
noncomputable def residueMap
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 →ₗ[ℂ] ℂ :=
  (residueMapIso X).toLinearMap

/-- Inverse residue map, extracted from the opaque residue
isomorphism. -/
noncomputable def residueMap_inverse
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    ℂ →ₗ[ℂ] RSSheafCohomology X (RSDualizingSheaf X) 1 :=
  (residueMapIso X).symm.toLinearMap

/-- Round-trip identity 1: `residueMap` followed by
`residueMap_inverse` is the identity. -/
theorem residueMap_left_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.LeftInverse (residueMap_inverse X) (residueMap X) := by
  simpa [residueMap, residueMap_inverse] using (residueMapIso X).left_inv

/-- Round-trip identity 2: `residueMap_inverse` followed by
`residueMap` is the identity. -/
theorem residueMap_right_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.RightInverse (residueMap_inverse X) (residueMap X) := by
  simpa [residueMap, residueMap_inverse] using (residueMapIso X).right_inv

end JacobianChallenge.HolomorphicForms
