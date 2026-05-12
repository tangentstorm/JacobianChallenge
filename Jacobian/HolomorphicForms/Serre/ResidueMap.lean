import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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

## Architecture note

The forward map, its inverse, and the two round-trip identities are
all derived from a single sorry'd `LinearEquiv` (`residueMapEquiv`),
so the round-trip properties follow from the equivalence structure
without additional sorry. The single remaining sorry sits in
`residueMapEquiv` itself, which is the frontier obligation.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** Canonical `ℂ`-linear equivalence
`H¹(X, K_X) ≃ₗ[ℂ] ℂ` on a compact connected Riemann surface.
This is the single sorry'd building block from which `residueMap`,
`residueMap_inverse`, and the round-trip identities are all
derived. -/
noncomputable def residueMapEquiv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 ≃ₗ[ℂ] ℂ := by
  exact sorry

/-- **Frontier `def`.** Residue / integration map
`H¹(X, K_X) → ℂ` on a compact connected Riemann surface.
Derived as the forward direction of `residueMapEquiv`. -/
noncomputable def residueMap
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    RSSheafCohomology X (RSDualizingSheaf X) 1 →ₗ[ℂ] ℂ :=
  (residueMapEquiv X).toLinearMap

/-- **Frontier `def`.** Inverse of the residue /
integration map. Derived as the inverse direction of
`residueMapEquiv`. -/
noncomputable def residueMap_inverse
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    ℂ →ₗ[ℂ] RSSheafCohomology X (RSDualizingSheaf X) 1 :=
  (residueMapEquiv X).symm.toLinearMap

/-- **Round-trip identity 1.** `residueMap` followed by
`residueMap_inverse` is the identity. Proved from
`residueMapEquiv.symm_apply_apply`. -/
theorem residueMap_left_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.LeftInverse (residueMap_inverse X) (residueMap X) := by
  intro x
  exact (residueMapEquiv X).symm_apply_apply x

/-- **Round-trip identity 2.** `residueMap_inverse` followed by
`residueMap` is the identity. Proved from
`residueMapEquiv.apply_symm_apply`. -/
theorem residueMap_right_inv
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    Function.RightInverse (residueMap_inverse X) (residueMap X) := by
  intro x
  exact (residueMapEquiv X).apply_symm_apply x

end JacobianChallenge.HolomorphicForms
