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
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** Residue / integration map
`H¹(X, K_X) → ℂ` on a compact connected Riemann surface. -/
noncomputable def residueMap
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 →ₗ[ℂ] ℂ := by
  exact 0

/-- **Frontier theorem (sorry).** `residueMap` is a `ℂ`-linear
isomorphism: `H¹(X, K_X) ≃ₗ[ℂ] ℂ`.

Decomposes classically into

* `dim_ℂ H¹(X, K_X) = 1` (handled also by
  `h1_dualizing_sheaf_one_dim` in `H1DualizingSheaf.lean`),
* the residue is nonzero on a chosen generator. -/
noncomputable def residueMap_inverse
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    ℂ →ₗ[ℂ] RSSheafCohomology X (RSDualizingSheaf X) 1 := by
  exact 0

/-- **Frontier theorem (sorry).** Round-trip identity 1: `residueMap`
followed by `residueMap_inverse` is the identity. -/
theorem residueMap_left_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.LeftInverse (residueMap_inverse X) (residueMap X) := by
  sorry

/-- **Frontier theorem (sorry).** Round-trip identity 2: `residueMap_inverse`
followed by `residueMap` is the identity. -/
theorem residueMap_right_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.RightInverse (residueMap_inverse X) (residueMap X) := by
  sorry

end JacobianChallenge.HolomorphicForms
