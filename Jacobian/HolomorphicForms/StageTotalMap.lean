import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Jacobian.HolomorphicForms.StageNormalization

/-!
# Total stage maps from normalized coordinates

This module records the C3 bookkeeping layer of the genus-zero Perron engine:
turn the normalized cut-domain coordinates into total maps
`X → OnePoint ℂ` by using a fixed filler value off the active cut domain.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
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

/--
Changing the off-domain filler does not change the total stage maps on any set
that is eventually contained in the cut domains.
-/
theorem stageTotalMapWithFiller_eventually_eqOn_of_eventually_subset_cutDomain
    {X : Type*} {cutDomain : ℕ → Set X}
    {normalizedCoordinate : ℕ → X → ℂ} {K : Set X}
    {filler₁ filler₂ : OnePoint ℂ}
    (hK : ∀ᶠ n in atTop, K ⊆ cutDomain n) :
    ∀ᶠ n in atTop,
      Set.EqOn
        ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₁) n)
        ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₂) n)
        K := by
  filter_upwards [hK] with n hn x hx
  have hxcut : x ∈ cutDomain n := hn hx
  simp [stageTotalMapWithFiller, hxcut]

/--
Uniform convergence on a set is unchanged by an eventually pointwise-equal
replacement of the sequence on that set.
-/
theorem tendstoUniformlyOn_congr_eventuallyEqOn
    {α β ι : Type*} [UniformSpace β]
    {F G : ι → α → β} {f : α → β} {p : Filter ι} {K : Set α}
    (hFG : ∀ᶠ n in p, Set.EqOn (F n) (G n) K) :
    TendstoUniformlyOn F f p K ↔ TendstoUniformlyOn G f p K := by
  constructor
  · intro hF
    exact hF.congr hFG
  · intro hG
    exact hG.congr (hFG.mono fun _ hn x hx => (hn hx).symm)

/--
Locally uniform convergence on a set is unchanged by an eventually
pointwise-equal replacement of the sequence on that set.
-/
theorem tendstoLocallyUniformlyOn_congr_eventuallyEqOn
    {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
    {F G : ι → α → β} {f : α → β} {p : Filter ι} {K : Set α}
    (hFG : ∀ᶠ n in p, Set.EqOn (F n) (G n) K) :
    TendstoLocallyUniformlyOn F f p K ↔
      TendstoLocallyUniformlyOn G f p K := by
  constructor
  · intro hF
    exact hF.congr_inseparable
      (hFG.mono fun _ hn x hx => Inseparable.of_eq (hn hx))
  · intro hG
    exact hG.congr_inseparable
      (hFG.mono fun _ hn x hx => Inseparable.of_eq (hn hx).symm)

/--
The choice of filler in `stageTotalMapWithFiller` does not affect uniform
convergence after applying any target reading, once the source set is eventually
inside the cut domains.
-/
theorem tendstoUniformlyOn_stageTotalMapWithFiller_iff
    {X β : Type*} [UniformSpace β] {cutDomain : ℕ → Set X}
    {normalizedCoordinate : ℕ → X → ℂ} {K : Set X}
    {filler₁ filler₂ : OnePoint ℂ} (targetChart : OnePoint ℂ → β)
    {limit : X → β}
    (hK : ∀ᶠ n in atTop, K ⊆ cutDomain n) :
    TendstoUniformlyOn
        (fun n x =>
          targetChart
            ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₁)
              n x))
        limit atTop K ↔
      TendstoUniformlyOn
        (fun n x =>
          targetChart
            ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₂)
              n x))
        limit atTop K := by
  exact tendstoUniformlyOn_congr_eventuallyEqOn
    ((stageTotalMapWithFiller_eventually_eqOn_of_eventually_subset_cutDomain
      (cutDomain := cutDomain) (normalizedCoordinate := normalizedCoordinate)
      (K := K) (filler₁ := filler₁) (filler₂ := filler₂) hK).mono
        fun _ hn x hx => congrArg targetChart (hn hx))

/--
The choice of filler in `stageTotalMapWithFiller` does not affect locally
uniform convergence after applying any target reading, once the source set is
eventually inside the cut domains.
-/
theorem tendstoLocallyUniformlyOn_stageTotalMapWithFiller_iff
    {X β : Type*} [TopologicalSpace X] [UniformSpace β]
    {cutDomain : ℕ → Set X} {normalizedCoordinate : ℕ → X → ℂ}
    {K : Set X} {filler₁ filler₂ : OnePoint ℂ}
    (targetChart : OnePoint ℂ → β) {limit : X → β}
    (hK : ∀ᶠ n in atTop, K ⊆ cutDomain n) :
    TendstoLocallyUniformlyOn
        (fun n x =>
          targetChart
            ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₁)
              n x))
        limit atTop K ↔
      TendstoLocallyUniformlyOn
        (fun n x =>
          targetChart
            ((stageTotalMapWithFiller cutDomain normalizedCoordinate filler₂)
              n x))
        limit atTop K := by
  exact tendstoLocallyUniformlyOn_congr_eventuallyEqOn
    ((stageTotalMapWithFiller_eventually_eqOn_of_eventually_subset_cutDomain
      (cutDomain := cutDomain) (normalizedCoordinate := normalizedCoordinate)
      (K := K) (filler₁ := filler₁) (filler₂ := filler₂) hK).mono
        fun _ hn x hx => congrArg targetChart (hn hx))

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

/--
Two C3 total-map payloads over the same normalized coordinates eventually agree
on any set eventually contained in the cut domains.
-/
theorem eventually_eqOn_of_eventually_subset_cutDomain
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    ∀ᶠ n in atTop,
      Set.EqOn (stageMaps₁.totalMap n) (stageMaps₂.totalMap n) K := by
  filter_upwards [hK] with n hn x hx
  have hxcut : x ∈ cutSystem.cutDomain n := hn hx
  rw [stageMaps₁.on_cutDomain n x hxcut, stageMaps₂.on_cutDomain n x hxcut]

/--
For two C3 payloads over the same normalized coordinates, target readings of
the total maps have equivalent uniform convergence on eventually contained
sets.
-/
theorem tendstoUniformlyOn_iff_of_eventually_subset_cutDomain
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {β : Type*} [UniformSpace β] (targetChart : OnePoint ℂ → β)
    {limit : X → β} {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    TendstoUniformlyOn
        (fun n x => targetChart (stageMaps₁.totalMap n x)) limit atTop K ↔
      TendstoUniformlyOn
        (fun n x => targetChart (stageMaps₂.totalMap n x)) limit atTop K := by
  exact tendstoUniformlyOn_congr_eventuallyEqOn
    ((eventually_eqOn_of_eventually_subset_cutDomain
      stageMaps₁ stageMaps₂ hK).mono
        fun _ hn x hx => congrArg targetChart (hn hx))

/--
For two C3 payloads over the same normalized coordinates, target readings of
the total maps have equivalent locally-uniform convergence on eventually
contained sets.
-/
theorem tendstoLocallyUniformlyOn_iff_of_eventually_subset_cutDomain
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {β : Type*} [UniformSpace β] (targetChart : OnePoint ℂ → β)
    {limit : X → β} {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    TendstoLocallyUniformlyOn
        (fun n x => targetChart (stageMaps₁.totalMap n x)) limit atTop K ↔
      TendstoLocallyUniformlyOn
        (fun n x => targetChart (stageMaps₂.totalMap n x)) limit atTop K := by
  exact tendstoLocallyUniformlyOn_congr_eventuallyEqOn
    ((eventually_eqOn_of_eventually_subset_cutDomain
      stageMaps₁ stageMaps₂ hK).mono
        fun _ hn x hx => congrArg targetChart (hn hx))

end StageTotalMaps

end JacobianChallenge.HolomorphicForms
