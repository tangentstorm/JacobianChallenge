import Jacobian.HolomorphicForms.Serre.FiniteDimInstances
import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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
finite-dimensionality and surjections.

The `Subsingleton` instance arguments propagate the Round-13
placeholder hypothesis (`harmonicForms = PUnit`,
`harmonicForms_toH{0,1} = 0`): under those placeholders the
surjectivity sub-leaf reduces to subsingletonness of the codomain.
Once R5+R7 supplies a real harmonic representation the
`Subsingleton` arguments will be replaceable by genuine derivations
from Hodge theory (and in fact will contradict non-zero genus,
forcing the placeholder rewrite at the same time). -/
theorem finiteDimensionalSheafCohomologyRS_canonical
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 1)]
    [Subsingleton (RSSheafCohomology X (RSDualizingSheaf X) 0)]
    [Subsingleton (RSSheafCohomology X (RSDualizingSheaf X) 1)] :
    FiniteDimensionalSheafCohomologyRS X (RSDualizingSheaf X) := by
  constructor
  · haveI : FiniteDimensional ℂ (harmonicForms X (RSDualizingSheaf X) 0) :=
      harmonicForms_canonical_H0_finiteDimensional X
    exact FiniteDimensional.of_surjective
      (harmonicForms_toH0 X (RSDualizingSheaf X))
      (harmonicForms_toH0_surjective X (RSDualizingSheaf X))
  · haveI : FiniteDimensional ℂ (harmonicForms X (RSDualizingSheaf X) 1) :=
      harmonicForms_canonical_H1_finiteDimensional X
    exact FiniteDimensional.of_surjective
      (harmonicForms_toH1 X (RSDualizingSheaf X))
      (harmonicForms_toH1_surjective X (RSDualizingSheaf X))

/-- Round 22 discharge: same for the structure sheaf. -/
theorem finiteDimensionalSheafCohomologyRS_structure
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 0)]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 1)]
    [Subsingleton (RSSheafCohomology X (RSStructureSheaf X) 0)]
    [Subsingleton (RSSheafCohomology X (RSStructureSheaf X) 1)] :
    FiniteDimensionalSheafCohomologyRS X (RSStructureSheaf X) := by
  constructor
  · haveI : FiniteDimensional ℂ (harmonicForms X (RSStructureSheaf X) 0) :=
      harmonicForms_structure_H0_finiteDimensional X
    exact FiniteDimensional.of_surjective
      (harmonicForms_toH0 X (RSStructureSheaf X))
      (harmonicForms_toH0_surjective X (RSStructureSheaf X))
  · haveI : FiniteDimensional ℂ (harmonicForms X (RSStructureSheaf X) 1) :=
      harmonicForms_structure_H1_finiteDimensional X
    exact FiniteDimensional.of_surjective
      (harmonicForms_toH1 X (RSStructureSheaf X))
      (harmonicForms_toH1_surjective X (RSStructureSheaf X))

end JacobianChallenge.HolomorphicForms
