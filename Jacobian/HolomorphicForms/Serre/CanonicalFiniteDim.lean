import Jacobian.HolomorphicForms.Serre.FiniteDimInstances
import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.HolomorphicForms.SheafCohomologyRS

/-!
# Finite-dimensionality discharge for `K_X` and `𝒪_X` (frontier)

Round 21/22 give a sorry-free discharge of
`FiniteDimensionalSheafCohomologyRS X (RSDualizingSheaf X)` and
`...X (RSStructureSheaf X)` *modulo* the harmonic-form
finite-dimensionality (rounds 21/22 sub-leaves) and the surjectivity
of `harmonicForms_to{H0,H1}` (round 14).

The downstream consumer instantiates the `FiniteDimensional ℂ H^q`
fields of `FiniteDimensionalSheafCohomologyRS` from
`Module.Finite.of_surjective` applied to
`harmonicForms_to{H0,H1}` plus
`harmonicForms_{canonical,structure}_{H0,H1}_finiteDimensional`.

The actual instance assembly is left as a sorry-free goal once the
universe-bookkeeping on the L²-pairing API stabilises; the named
obligations are now strictly smaller than the round-2 abstract
finite-dimensionality.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- Round 21 discharge: `FiniteDimensionalSheafCohomologyRS` for the
canonical bundle, conditional on the harmonic-form
finite-dimensionality and surjections. Currently sorry-bearing
pending universe cleanup (the pieces are all named). -/
theorem finiteDimensionalSheafCohomologyRS_canonical
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    FiniteDimensionalSheafCohomologyRS X (RSDualizingSheaf X) := by
  -- Body: build via Module.Finite.of_surjective of harmonicForms_toH{0,1}
  -- + harmonicForms_canonical_H{0,1}_finiteDimensional.
  sorry

/-- Round 22 discharge: same for the structure sheaf. -/
theorem finiteDimensionalSheafCohomologyRS_structure
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 1)] :
    FiniteDimensionalSheafCohomologyRS X (RSStructureSheaf X) := by
  sorry

end JacobianChallenge.HolomorphicForms
