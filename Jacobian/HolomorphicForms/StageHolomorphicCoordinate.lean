import Jacobian.HolomorphicForms.StageHarmonicConjugate

/-!
# Stage holomorphic coordinates from harmonic dipoles

This module records the B5 statement-level payload for complex coordinate
candidates built from the B2 harmonic potentials and B4 single-valued
conjugates.  It stops before normalization, noncollapse, Cauchy estimates, and
Montel extraction.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

/--
Stage-local holomorphicity predicate for a complex coordinate candidate on a
cut domain.
-/
def StageHolomorphicOnCut
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (cutDomain : Set X) (coordinate : X → ℂ) : Prop :=
  ∀ x, x ∈ cutDomain → IsHolomorphicInChartReal X coordinate x

/--
The pointwise formula tying a complex coordinate candidate to the B2 harmonic
potential and B4 conjugate.
-/
def StageCoordinateFormula
    (X : Type*) (potential conjugate : X → ℝ) (coordinate : X → ℂ) : Prop :=
  ∀ x, coordinate x = (potential x : ℂ) + Complex.I * (conjugate x : ℂ)

/--
Selected-compact readiness inherited by the holomorphic coordinate package:
the selected compactum lies in the cut domain, avoids the cuts, and the
coordinate is holomorphic at every point of it.
-/
def StageCoordinateSelectedCompactReady
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (K cutDomain cutSet : Set X) (coordinate : X → ℂ) : Prop :=
  StageConjugateSelectedCompactReady X K cutDomain cutSet ∧
    ∀ x, x ∈ K → IsHolomorphicInChartReal X coordinate x

/--
The B5 holomorphic-coordinate payload for all cut stages.

It records one complex candidate per stage, its pointwise formula from the B2
potential and B4 conjugate, chart-local holomorphicity on the cut domain,
compatibility with the B4 conjugacy interface, and inherited normalization and
selected-compact readiness needed by later normalization and chart-reading
nodes.
-/
structure StageHolomorphicCoordinates
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles)
    (cutSystem : StageMarkedCutSystem X marked selected exhaustion)
    (dirichlet :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl)
    (conjugates :
      StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet) where
  coordinate : ℕ → X → ℂ
  coordinate_formula :
    ∀ n, StageCoordinateFormula X (dirichlet.harmonicPotential n)
      (conjugates.harmonicConjugate n) (coordinate n)
  holomorphicOnCut :
    ∀ n, StageHolomorphicOnCut X (cutSystem.cutDomain n) (coordinate n)
  conjugateOnCut :
    ∀ n, StageConjugateOnCut X marked (cutSystem.cutDomain n)
      (dirichlet.harmonicPotential n) (conjugates.harmonicConjugate n)
  conjugateOnCut_eq :
    ∀ n, conjugateOnCut n = conjugates.conjugateOnCut n
  base_value :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      coordinate n marked.base = 0
  eventually_selectedReady :
    ∀ i, ∀ᶠ n in Filter.atTop,
      StageCoordinateSelectedCompactReady X (selected.compact i)
        (cutSystem.cutDomain n) (cutSystem.cutSet n) (coordinate n)
  selectedReadyBound :
    ∀ i, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      StageCoordinateSelectedCompactReady X (selected.compact i)
        (cutSystem.cutDomain n) (cutSystem.cutSet n) (coordinate n)

namespace StageHolomorphicCoordinates

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}
variable {marked : GenusZeroStageMarkedData X e}
variable {selected : StageSelectedCompactFamily X}
variable {exhaustion : StageBorderedExhaustion X selected}
variable {profiles : GenusZeroStageDipoleProfiles X e marked}
variable {boundaryControl :
  StageDipoleBoundaryControl X e marked selected exhaustion profiles}
variable {cutSystem : StageMarkedCutSystem X marked selected exhaustion}
variable {dirichlet :
  StageDirichletHarmonicSolution X e marked selected exhaustion profiles
    boundaryControl}
variable {conjugates :
  StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
    boundaryControl cutSystem dirichlet}

/-- On selected compacta, the coordinate package retains B4 cut readiness. -/
theorem selectedCompact_cutReady
    (coords :
      StageHolomorphicCoordinates X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet conjugates)
    {i : selected.Index} {n : ℕ}
    (hready :
      StageCoordinateSelectedCompactReady X (selected.compact i)
        (cutSystem.cutDomain n) (cutSystem.cutSet n) (coords.coordinate n)) :
    StageConjugateSelectedCompactReady X (selected.compact i)
      (cutSystem.cutDomain n) (cutSystem.cutSet n) :=
  hready.1

end StageHolomorphicCoordinates

/--
B5 frontier obligation: package the holomorphic coordinate candidates from
the B2 harmonic potentials and B4 conjugates.

This is intentionally narrower than stage-map normalization, noncollapse,
Cauchy estimates, and Montel extraction.
-/
theorem exists_stageHolomorphicCoordinatesFromHarmonicDipole
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles)
    (cutSystem : StageMarkedCutSystem X marked selected exhaustion)
    (dirichlet :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl)
    (conjugates :
      StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet) :
    Nonempty
      (StageHolomorphicCoordinates X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet conjugates) := by
  sorry

end JacobianChallenge.HolomorphicForms
