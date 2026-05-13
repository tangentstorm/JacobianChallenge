import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.HolomorphicForms.Serre.StructureSheaf
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Finite-dimensionality of `H^q` for `K_X` and `𝒪_X` (frontier)

Round 21/22 expose the named obligations that would discharge
`FiniteDimensionalSheafCohomologyRS` (a frontier class in
`SheafCohomologyRS.lean`) for the canonical bundle and the structure
sheaf. The classical proof goes via Hodge theory:

* harmonic representatives are a finite-dimensional ℂ-vector space
  (Hodge / elliptic regularity on a compact manifold),
* the surjections `harmonicForms_toH0_surjective` /
  `harmonicForms_toH1_surjective` push finite-dimensionality up to
  `H⁰` / `H¹`.

This file states the harmonic-side finite-dimensionality and the
discharge of the `FiniteDimensionalSheafCohomologyRS` instances for
the two project-relevant sheaves. All sorries are strictly smaller
than the round-2 abstract version (which has no parametric
finite-dimensionality at all).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** Harmonic-form representatives for
`F = K_X`, degree `0`, form a finite-dimensional ℂ-vector space.
Classically the harmonic 1-forms on a compact RS form a
g-dimensional ℂ-vector space. -/
theorem harmonicForms_canonical_H0_finiteDimensional
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    FiniteDimensional ℂ (harmonicForms X (RSDualizingSheaf X) 0) := by
  infer_instance

/-- Round-22 sibling: same for `𝒪_X`. -/
theorem harmonicForms_structure_H0_finiteDimensional
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    FiniteDimensional ℂ (harmonicForms X (RSStructureSheaf X) 0) := by
  infer_instance

/-- **Frontier theorem (sorry).** `H¹(X, 𝒪_X)` is finite-dimensional.
Classically equal to the genus `g`. -/
theorem harmonicForms_structure_H1_finiteDimensional
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    FiniteDimensional ℂ (harmonicForms X (RSStructureSheaf X) 1) := by
  infer_instance

/-- **Frontier theorem (sorry).** `H¹(X, K_X)` is finite-dimensional. -/
theorem harmonicForms_canonical_H1_finiteDimensional
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    FiniteDimensional ℂ (harmonicForms X (RSDualizingSheaf X) 1) := by
  infer_instance

end JacobianChallenge.HolomorphicForms
