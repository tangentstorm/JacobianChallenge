import Jacobian.HolomorphicForms.StageTotalMap
import Jacobian.HolomorphicForms.UniformizationLocal

/-!
# Stage chart readings

This module records the D-row chart-reading interface for the genus-zero Perron
engine.  It names the target-chart reading of a C3 total stage family once, then
exports the green transport lemmas that make the off-domain filler irrelevant on
eventually contained source sets.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
open scoped Topology

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
The target-chart reading of a total stage family.

This is the common `fun n x => targetChart (F n x)` shape consumed by the
Montel chart-ball and filler-irrelevance interfaces.
-/
noncomputable def stageChartReading
    {β : Type*}
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → β) : ℕ → X → β :=
  fun n x => targetChart (stageMaps.totalMap n x)

/-- On the cut domain, a chart reading is the target chart applied to the
finite normalized coordinate. -/
theorem stageChartReading_on_cutDomain
    {β : Type*}
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → β) {n : ℕ} {x : X}
    (hx : x ∈ cutSystem.cutDomain n) :
    stageChartReading stageMaps targetChart n x =
      targetChart ((normalized.normalizedCoordinate n x : OnePoint ℂ)) := by
  rw [stageChartReading, StageTotalMaps.on_cutDomain_apply stageMaps hx]

/--
Two total-map payloads over the same normalized coordinates give the same chart
readings on any set eventually contained in the cut domains.
-/
theorem stageChartReading_eventually_eqOn_of_eventually_subset_cutDomain
    {β : Type*}
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → β) {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    ∀ᶠ n in atTop,
      Set.EqOn (stageChartReading stageMaps₁ targetChart n)
        (stageChartReading stageMaps₂ targetChart n) K := by
  exact
    (StageTotalMaps.eventually_eqOn_of_eventually_subset_cutDomain
      stageMaps₁ stageMaps₂ hK).mono
      fun _ hn x hx => congrArg targetChart (hn hx)

/--
Filler-irrelevance for uniform convergence, stated in terms of
`stageChartReading`.
-/
theorem stageChartReading_tendstoUniformlyOn_iff_of_eventually_subset_cutDomain
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {β : Type*} [UniformSpace β] (targetChart : OnePoint ℂ → β)
    {limit : X → β} {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    TendstoUniformlyOn (stageChartReading stageMaps₁ targetChart) limit atTop K ↔
      TendstoUniformlyOn (stageChartReading stageMaps₂ targetChart) limit atTop K := by
  change
    TendstoUniformlyOn (fun n x => targetChart (stageMaps₁.totalMap n x))
        limit atTop K ↔
      TendstoUniformlyOn (fun n x => targetChart (stageMaps₂.totalMap n x))
        limit atTop K
  exact
    StageTotalMaps.tendstoUniformlyOn_iff_of_eventually_subset_cutDomain
      stageMaps₁ stageMaps₂ targetChart hK

/--
Filler-irrelevance for locally uniform convergence, stated in terms of
`stageChartReading`.
-/
theorem stageChartReading_tendstoLocallyUniformlyOn_iff_of_eventually_subset_cutDomain
    (stageMaps₁ stageMaps₂ :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    {β : Type*} [UniformSpace β] (targetChart : OnePoint ℂ → β)
    {limit : X → β} {K : Set X}
    (hK : ∀ᶠ n in atTop, K ⊆ cutSystem.cutDomain n) :
    TendstoLocallyUniformlyOn (stageChartReading stageMaps₁ targetChart)
        limit atTop K ↔
      TendstoLocallyUniformlyOn (stageChartReading stageMaps₂ targetChart)
        limit atTop K := by
  change
    TendstoLocallyUniformlyOn
        (fun n x => targetChart (stageMaps₁.totalMap n x)) limit atTop K ↔
      TendstoLocallyUniformlyOn
        (fun n x => targetChart (stageMaps₂.totalMap n x)) limit atTop K
  exact
    StageTotalMaps.tendstoLocallyUniformlyOn_iff_of_eventually_subset_cutDomain
      stageMaps₁ stageMaps₂ targetChart hK

/-- Uniform convergence of chart readings is invariant under eventually-equal
restriction to the source set. -/
theorem tendstoUniformlyOn_stageChartReading_congr_eventuallyEqOn
    {β : Type*} [UniformSpace β]
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → β) {G : ℕ → X → β} {limit : X → β}
    {K : Set X}
    (hG :
      ∀ᶠ n in atTop,
        Set.EqOn (stageChartReading stageMaps targetChart n) (G n) K) :
    TendstoUniformlyOn (stageChartReading stageMaps targetChart) limit atTop K ↔
      TendstoUniformlyOn G limit atTop K :=
  tendstoUniformlyOn_congr_eventuallyEqOn hG

/-- Locally uniform convergence of chart readings is invariant under
eventually-equal restriction to the source set. -/
theorem tendstoLocallyUniformlyOn_stageChartReading_congr_eventuallyEqOn
    {β : Type*} [UniformSpace β]
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → β) {G : ℕ → X → β} {limit : X → β}
    {K : Set X}
    (hG :
      ∀ᶠ n in atTop,
        Set.EqOn (stageChartReading stageMaps targetChart n) (G n) K) :
    TendstoLocallyUniformlyOn (stageChartReading stageMaps targetChart)
        limit atTop K ↔
      TendstoLocallyUniformlyOn G limit atTop K :=
  tendstoLocallyUniformlyOn_congr_eventuallyEqOn hG

/--
Uniform Cauchy-bound shape for a chart reading on a selected compactum.

The bound is phrased over an arbitrary Cauchy-circle parametrization
`circleSource : ℂ → X`, so downstream chart-ball tasks can instantiate it with
the relevant source chart inverse.
-/
def StageChartReadingUniformCauchyBound
    (reading : ℕ → X → ℂ) (circleSource : ℂ → X)
    (center : ℂ) (cauchyRadius : ℝ) : Prop :=
  ∃ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, N ≤ n →
      ∀ z ∈ Metric.sphere center cauchyRadius,
        ‖reading n (circleSource z)‖ ≤ M

/--
D-row frontier obligation: uniform Cauchy bounds for stage chart readings on
eventually contained selected compacta.

The explicit inputs are the A4 concrete containment/avoidance bound for the
source compactum and the C/B compact-bound handles that later maximum-principle
estimates consume.
-/
theorem stageChartReading_uniform_cauchy_bound
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → ℂ) (i : selected.Index)
    {K : Set X} (circleSource : ℂ → X) {center : ℂ} {cauchyRadius : ℝ}
    (hcircle : ∀ z ∈ Metric.sphere center cauchyRadius, circleSource z ∈ K)
    (hA4 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K ⊆ cutSystem.cutDomain n ∧ Disjoint K (cutSystem.cutSet n))
    (hboundary :
      ∀ n, dirichlet.boundaryCompactBound n = boundaryControl.compactBound n)
    (hcompact : ∀ n, StageDipoleCompactBound X (exhaustion.stage n)
      (dirichlet.harmonicPotential n)) :
    StageChartReadingUniformCauchyBound
      (stageChartReading stageMaps targetChart) circleSource center cauchyRadius := by
  sorry

/--
Conditional chart-ball packaging for stage chart readings.

The D-row analytic work supplies the closed-ball continuity/open-ball
differentiability hypothesis; this declaration performs the standard green
entry into the existing `ChartBallPowerSeries` API.
-/
noncomputable def stageChartReading_chartBallPowerSeries
    (stageMaps :
      StageTotalMaps X e marked selected exhaustion profiles boundaryControl
        cutSystem dirichlet conjugates coordinates normalized)
    (targetChart : OnePoint ℂ → ℂ) (sourceChart : ℂ → X)
    {center : ℂ} {radius : NNReal}
    (hradius : 0 < radius)
    (hdiff :
      DiffContOnCl ℂ
        (fun z => stageChartReading stageMaps targetChart 0 (sourceChart z))
        (Metric.ball center (radius : ℝ)))
    (_hbound :
      ∀ cauchyRadius : ℝ,
        StageChartReadingUniformCauchyBound
          (stageChartReading stageMaps targetChart) sourceChart center
          cauchyRadius) :
    ChartBallPowerSeries :=
  ChartBallPowerSeries.ofDiffContOnCl hradius hdiff

end JacobianChallenge.HolomorphicForms
