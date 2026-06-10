import Jacobian.HolomorphicForms.GenusZeroClassification

/-!
# Montel local patch realization

This file provides the **green existence provider** for the open blueprint node
`lem:montel-local-patch-realization`
(`JacobianChallenge.HolomorphicForms.GenusZeroLocalMontelPatchRealization`).

The realization structure ties an abstract global gluing patch to a local
normalized Montel chart patch: the source chart lands in the chart-ball domain,
the patch coordinate is the chart-ball limit in that source coordinate, and the
inverse branch agrees with the local inverse supplied by the inverse-function
theorem chart package.

The construction is built *from the chart-ball substrate up* — it takes a smooth
source chart on `X` together with a section, packages the global patch whose
coordinate is `chartBall.toFun ∘ sourceChart` and whose inverse branch is
`sourceSection ∘ localOpen.symm`, and then the realization holds by
construction.  Crucially, it does **not** read any field of
`GenusZeroNormalizedMontelPatchSelector` (the circular trap).

The single genuine analytic obligation discharged here is the smoothness of the
packaged patch coordinate `chartBall.toFun ∘ sourceChart`: the chart-ball map is
holomorphic on the open ball (hence analytic, hence `C^∞`), and composing with
the smooth source chart that lands in the ball gives a `ContMDiffOn` coordinate.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- The chart-ball map of a Montel local patch is `ContMDiffOn` (between the
`ℂ`-model manifold and itself) on the open chart ball.  This is the analytic
core: the packaged map is holomorphic on the open ball (`DiffContOnCl` restricts
to `DifferentiableOn` on the interior), hence analytic, hence `C^∞`. -/
theorem ChartBallPowerSeries.contMDiffOn_toFun_ball (chartBall : ChartBallPowerSeries) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞)
      chartBall.toFun (Metric.ball chartBall.center (chartBall.radius : ℝ)) := by
  rw [contMDiffOn_iff_contDiffOn]
  have hdiff : DifferentiableOn ℂ chartBall.toFun
      (Metric.ball chartBall.center (chartBall.radius : ℝ)) :=
    chartBall.diffContOnCl.differentiableOn
  have han : AnalyticOnNhd ℂ chartBall.toFun
      (Metric.ball chartBall.center (chartBall.radius : ℝ)) :=
    hdiff.analyticOnNhd Metric.isOpen_ball
  exact han.contDiffOn (Metric.isOpen_ball.uniqueDiffOn)

/--
The packaged global gluing patch whose coordinate is the chart-ball Montel limit
in the supplied source coordinate, and whose inverse branch is the supplied
section composed with the local inverse-function-theorem chart inverse.

The source chart is required to be smooth on the patch source and to land in the
open chart ball; the chart-ball map is then composed in to give the patch
coordinate, with smoothness provided by
`ChartBallPowerSeries.contMDiffOn_toFun_ball`.
-/
noncomputable def montelRealizationPatch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (source : Set X) (isOpen_source : IsOpen source)
    (sourceChart : X → ℂ) (sourceSection : ℂ → X)
    (sourceChart_contMDiffOn :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) sourceChart source)
    (sourceChart_mem_ball :
      ∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center (localPatch.chartBall.radius : ℝ)) :
    GenusZeroGlobalGluingPatch X where
  source := source
  isOpen_source := isOpen_source
  targetChart := localPatch.targetChart
  targetChart_standard := localPatch.targetChart_standard
  coord := fun x => localPatch.chartBall.toFun (sourceChart x)
  invCoord := fun z => sourceSection (localPatch.localChart.localOpen.symm z)
  coord_contMDiffOn :=
    (localPatch.chartBall.contMDiffOn_toFun_ball).comp sourceChart_contMDiffOn
      (fun x hx => sourceChart_mem_ball x hx)

/--
**Montel local patch realization (green provider).**

Given a Montel local chart patch and a smooth source chart on the patch source
that lands in the chart ball, together with a section that inverts the source
chart on the values produced by the local inverse-function-theorem chart, the
packaged patch `montelRealizationPatch` is genuinely realized by the local
normalized Montel chart.

All four realization fields hold by construction: the source chart is the
supplied smooth chart, it lands in the chart ball by hypothesis, the patch
coordinate is `chartBall.toFun ∘ sourceChart` definitionally, and the inverse
branch agrees with the local inverse by the section hypothesis.
-/
noncomputable def montelLocalPatchRealization
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (source : Set X) (isOpen_source : IsOpen source)
    (sourceChart : X → ℂ) (sourceSection : ℂ → X)
    (sourceChart_contMDiffOn :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) sourceChart source)
    (sourceChart_mem_ball :
      ∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center (localPatch.chartBall.radius : ℝ))
    (section_localInverse :
      ∀ z, z ∈ localPatch.targetChart.target →
        sourceChart (sourceSection (localPatch.localChart.localOpen.symm z)) =
          localPatch.localChart.localOpen.symm z) :
    GenusZeroLocalMontelPatchRealization
      (montelRealizationPatch localPatch source isOpen_source sourceChart sourceSection
        sourceChart_contMDiffOn sourceChart_mem_ball)
      localPatch where
  sourceChart := sourceChart
  sourceChart_contMDiffOn := sourceChart_contMDiffOn
  sourceChart_mem_chartBall := sourceChart_mem_ball
  coord_eq_chartBall := fun _ _ => rfl
  invCoord_sourceChart_eq_localInverse := section_localInverse

/--
On the local source neighborhood, the chart-ball map agrees with the local
inverse-function-theorem partial homeomorphism.  This is the bridge between the
analytic packaged map `chartBall.toFun` and the topological partial homeomorph
`localOpen` used to express the inverse branch; it comes directly from the
`toFun_eq_on_source` field of the local chart data.
-/
theorem ChartBallPowerSeries.toFun_eq_localOpen_on_source
    (chartBall : ChartBallPowerSeries)
    (lc : chartBall.LocalNormalizedChartHomeomorphData)
    {w : ℂ} (hw : w ∈ lc.localOpen.source) :
    chartBall.toFun w = lc.localOpen w := by
  have h := lc.toFun_eq_on_source ⟨w, hw⟩
  rw [lc.homeomorph_eq] at h
  simp only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] at h
  exact h.symm

/--
**Local right-inverse identity for the realized patch.**

On the local chart target, the realized patch coordinate undoes its inverse
branch: `coord (invCoord z) = z`.  This is the local right-inverse fact the
global-gluing substrate consumes (`local_right_inverse_on_target_chart`), proved
purely from the chart-ball substrate: the section hypothesis pulls the source
chart back to `localOpen.symm z`, the chart-ball map then agrees with `localOpen`
there, and `OpenPartialHomeomorph.right_inv` closes the round trip.
-/
theorem montelRealizationPatch_coord_invCoord
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (source : Set X) (isOpen_source : IsOpen source)
    (sourceChart : X → ℂ) (sourceSection : ℂ → X)
    (sourceChart_contMDiffOn :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) sourceChart source)
    (sourceChart_mem_ball :
      ∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center (localPatch.chartBall.radius : ℝ))
    (section_localInverse :
      ∀ z, z ∈ localPatch.localChart.localOpen.target →
        sourceChart (sourceSection (localPatch.localChart.localOpen.symm z)) =
          localPatch.localChart.localOpen.symm z)
    {z : ℂ} (hz : z ∈ localPatch.localChart.localOpen.target) :
    (montelRealizationPatch localPatch source isOpen_source sourceChart sourceSection
        sourceChart_contMDiffOn sourceChart_mem_ball).coord
      ((montelRealizationPatch localPatch source isOpen_source sourceChart sourceSection
        sourceChart_contMDiffOn sourceChart_mem_ball).invCoord z) = z := by
  show localPatch.chartBall.toFun
      (sourceChart (sourceSection (localPatch.localChart.localOpen.symm z))) = z
  rw [section_localInverse z hz]
  have hmem : localPatch.localChart.localOpen.symm z ∈
      localPatch.localChart.localOpen.source :=
    localPatch.localChart.localOpen.map_target hz
  rw [localPatch.chartBall.toFun_eq_localOpen_on_source localPatch.localChart hmem,
    localPatch.localChart.localOpen.right_inv hz]

/--
**Local left-inverse identity for the realized patch.**

On the patch source, the realized patch inverse branch undoes its coordinate:
`invCoord (coord x) = x`.  This is the local left-inverse fact the global-gluing
substrate consumes (`local_left_inverse_on_patch`).  It rests on the chart-ball
substrate — `localOpen.symm (chartBall.toFun (sourceChart x)) = sourceChart x`
via `left_inv` on the domain ball — together with one honest section round-trip
hypothesis `sourceSection (sourceChart x) = x` that a caller supplies (mirroring
the input style of `section_localInverse` in the accepted provider).
-/
theorem montelRealizationPatch_invCoord_coord
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (source : Set X) (isOpen_source : IsOpen source)
    (sourceChart : X → ℂ) (sourceSection : ℂ → X)
    (sourceChart_contMDiffOn :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) sourceChart source)
    (sourceChart_mem_ball :
      ∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center (localPatch.chartBall.radius : ℝ))
    (sourceChart_mem_domainBall :
      ∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center localPatch.localChart.domainRadius)
    (section_sourceChart :
      ∀ x, x ∈ source → sourceSection (sourceChart x) = x)
    {x : X} (hx : x ∈ source) :
    (montelRealizationPatch localPatch source isOpen_source sourceChart sourceSection
        sourceChart_contMDiffOn sourceChart_mem_ball).invCoord
      ((montelRealizationPatch localPatch source isOpen_source sourceChart sourceSection
        sourceChart_contMDiffOn sourceChart_mem_ball).coord x) = x := by
  show sourceSection
      (localPatch.localChart.localOpen.symm
        (localPatch.chartBall.toFun (sourceChart x))) = x
  have hsrc : sourceChart x ∈ localPatch.localChart.localOpen.source :=
    localPatch.localChart.source_ball_subset (sourceChart_mem_domainBall x hx)
  have hval : localPatch.chartBall.toFun (sourceChart x) =
      localPatch.localChart.localOpen (sourceChart x) :=
    localPatch.chartBall.toFun_eq_localOpen_on_source localPatch.localChart hsrc
  rw [hval, localPatch.localChart.localOpen.left_inv hsrc, section_sourceChart x hx]

end JacobianChallenge.HolomorphicForms
