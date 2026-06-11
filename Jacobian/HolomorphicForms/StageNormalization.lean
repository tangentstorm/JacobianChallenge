import Jacobian.HolomorphicForms.StageHolomorphicCoordinate

/-!
# Stage normalization and noncollapse interface

This module records the C1/C2 statement-level payload for the genus-zero
Perron engine.  It consumes the B5 holomorphic coordinate candidates on cut
stages and exposes normalized stage coordinates with chart-local center-value
and derivative data.  The analytic proof of existence remains the named
frontier obligation below.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

/--
The chart-local reading of a stage coordinate at a source point.
-/
noncomputable def StageCoordinateChartReading
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (sourcePoint : X) (coordinate : X → ℂ) : ℂ → ℂ :=
  fun z => coordinate ((chartAt ℂ sourcePoint).symm z)

/--
Chart-local normalization at a source point: the local reading has value `0`
and derivative `1` at the chart center.
-/
def StageCoordinateChartNormalization
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (sourcePoint : X) (coordinate : X → ℂ) : Prop :=
  StageCoordinateChartReading X sourcePoint coordinate
      ((chartAt ℂ sourcePoint) sourcePoint) = 0 ∧
    HasDerivAt (StageCoordinateChartReading X sourcePoint coordinate) 1
      ((chartAt ℂ sourcePoint) sourcePoint)

/--
Inversion-end chart normalization: the reciprocal coordinate, not the
coordinate itself, has value `0` and derivative `1` at the marked infinity
chart center.
-/
def StageCoordinateInvertedChartNormalization
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (sourcePoint : X) (coordinate : X → ℂ) : Prop :=
  StageCoordinateChartNormalization X sourcePoint
    (fun x => (coordinate x)⁻¹)

/--
Pre-normalization noncollapse at a source point: the chart-local reading has
some nonzero derivative at the chart center.
-/
def StageCoordinateNoncollapse
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (sourcePoint : X) (coordinate : X → ℂ) : Prop :=
  ∃ slope : ℂ, slope ≠ 0 ∧
    HasDerivAt (StageCoordinateChartReading X sourcePoint coordinate) slope
      ((chartAt ℂ sourcePoint) sourcePoint)

/--
The normalized coordinate is obtained from the B5 coordinate by a nonzero
affine rescaling on the active cut domain.
-/
def StageCoordinateAffineNormalization
    (X : Type*) (cutDomain : Set X) (raw normalized : X → ℂ) : Prop :=
  ∃ scale shift : ℂ, scale ≠ 0 ∧
    ∀ x, x ∈ cutDomain → normalized x = scale * (raw x - shift)

/--
The C1/C2 normalized-coordinate payload for all cut stages.

It records one normalized complex coordinate per stage, relates it to the B5
coordinate by nonzero affine rescaling on the cut domain, preserves
holomorphicity there, fixes the base/identity-chart normalization, records
the compatible reciprocal normalization at the inversion end, and exposes
noncollapse of the pre-normalized B5 coordinate at the base point.
-/
structure StageNormalizedHolomorphicCoordinates
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
        boundaryControl cutSystem dirichlet)
    (coordinates :
      StageHolomorphicCoordinates X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet conjugates) where
  normalizedCoordinate : ℕ → X → ℂ
  affine_normalized :
    ∀ n, StageCoordinateAffineNormalization X (cutSystem.cutDomain n)
      (coordinates.coordinate n) (normalizedCoordinate n)
  holomorphicOnCut :
    ∀ n, StageHolomorphicOnCut X (cutSystem.cutDomain n)
      (normalizedCoordinate n)
  /-- Redundant with `identity_chart_normalized`, but convenient for C3. -/
  base_value :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      normalizedCoordinate n marked.base = 0
  identity_chart_normalized :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      StageCoordinateChartNormalization X marked.base (normalizedCoordinate n)
  inversion_chart_compatible :
    ∀ n, StageCoordinateInvertedChartNormalization X marked.Pinf
      (normalizedCoordinate n)
  coordinate_noncollapse :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      StageCoordinateNoncollapse X marked.base (coordinates.coordinate n)

/--
C1/C2 frontier obligation: normalize the B5 holomorphic stage coordinates and
prove the noncollapse derivative data needed by later chart-reading and
Montel extraction.
-/
theorem exists_stageNormalizedHolomorphicCoordinates
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
        boundaryControl cutSystem dirichlet)
    (coordinates :
      StageHolomorphicCoordinates X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet conjugates) :
    Nonempty
      (StageNormalizedHolomorphicCoordinates X e marked selected exhaustion
        profiles boundaryControl cutSystem dirichlet conjugates coordinates) := by
  sorry

end JacobianChallenge.HolomorphicForms
