import Jacobian.HolomorphicForms.StageNormalization

/-!
# Total stage maps from normalized coordinates

This module records the C3 bookkeeping layer of the genus-zero Perron engine:
turn the normalized cut-domain coordinates into total maps
`X → OnePoint ℂ` by using a fixed filler value off the active cut domain.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

/--
Extend normalized stage coordinates to total `OnePoint ℂ`-valued maps by a
fixed filler off each cut domain.
-/
noncomputable def stageTotalMapWithFiller
    {X : Type*} (cutDomain : ℕ → Set X)
    (normalizedCoordinate : ℕ → X → ℂ) (filler : OnePoint ℂ) :
    ℕ → X → OnePoint ℂ :=
  fun n x => by
    classical
    if x ∈ cutDomain n then
      exact (normalizedCoordinate n x : OnePoint ℂ)
    else
      exact filler

/--
The C3 total-stage-map payload.

It packages the total `OnePoint ℂ`-valued stage family, records the fixed
filler used away from the cut domain, and exposes the defining equations on
and off the cut domain.  The base-value field is the convenient C3 form of
the C1/C2 normalization data after lifting finite values to `OnePoint ℂ`.
-/
structure StageTotalMaps
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
        boundaryControl cutSystem dirichlet conjugates)
    (normalized :
      StageNormalizedHolomorphicCoordinates X e marked selected exhaustion
        profiles boundaryControl cutSystem dirichlet conjugates coordinates) where
  totalMap : ℕ → X → OnePoint ℂ
  filler : OnePoint ℂ
  on_cutDomain :
    ∀ n x, x ∈ cutSystem.cutDomain n →
      totalMap n x = (normalized.normalizedCoordinate n x : OnePoint ℂ)
  off_cutDomain :
    ∀ n x, x ∉ cutSystem.cutDomain n →
      totalMap n x = filler
  base_value :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      totalMap n marked.base = ((0 : ℂ) : OnePoint ℂ)

namespace StageTotalMaps

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
variable {coordinates :
  StageHolomorphicCoordinates X e marked selected exhaustion profiles
    boundaryControl cutSystem dirichlet conjugates}
variable {normalized :
  StageNormalizedHolomorphicCoordinates X e marked selected exhaustion
    profiles boundaryControl cutSystem dirichlet conjugates coordinates}

/-- On the cut domain, total maps retain the finite normalized coordinate. -/
theorem on_cutDomain_apply
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {n : ℕ} {x : X} (hx : x ∈ cutSystem.cutDomain n) :
    stageMaps.totalMap n x =
      (normalized.normalizedCoordinate n x : OnePoint ℂ) :=
  stageMaps.on_cutDomain n x hx

end StageTotalMaps

/--
C3 constructor: the total stage maps are obtained directly from the normalized
coordinates by filling outside the cut domain with a fixed value.
-/
theorem exists_stageTotalMaps
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
        boundaryControl cutSystem dirichlet conjugates)
    (normalized :
      StageNormalizedHolomorphicCoordinates X e marked selected exhaustion
        profiles boundaryControl cutSystem dirichlet conjugates coordinates) :
    Nonempty
      (StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized) := by
  let filler : OnePoint ℂ := ((0 : ℂ) : OnePoint ℂ)
  let totalMap :=
    stageTotalMapWithFiller cutSystem.cutDomain normalized.normalizedCoordinate
      filler
  refine ⟨{
    totalMap := totalMap
    filler := filler
    on_cutDomain := ?_
    off_cutDomain := ?_
    base_value := ?_
  }⟩
  · intro n x hx
    simp [totalMap, stageTotalMapWithFiller, hx]
  · intro n x hx
    simp [totalMap, stageTotalMapWithFiller, hx]
  · intro n hn
    rw [show totalMap n marked.base =
      (normalized.normalizedCoordinate n marked.base : OnePoint ℂ) by
        simp [totalMap, stageTotalMapWithFiller, hn]]
    rw [normalized.base_value n hn]

end JacobianChallenge.HolomorphicForms
