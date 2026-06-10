import Jacobian.HolomorphicForms.MontelLocalPatchRealization

/-!
# Montel source-chart cover package (Phase-0 item 5)

This file supplies the **caller package** for the genus-zero Montel realization:
given one local normalized Montel chart patch together with an honest source
chart on `X` realizing its chart-ball coordinate, it produces the full
hypothesis list consumed by
`JacobianChallenge.HolomorphicForms.montelRealizedPatch_of_sourceChartLocalSection`
(`MontelLocalPatchRealization.lean`).

It is stated **per chart-ball datum, abstractly** — the selected patches do not
exist yet; the global construction (`GenusZeroUniformization.lean`, jc1) selects
them and instantiates this package once per selected patch.  Nothing here
references the global approximating sequence, the topological homeomorphism, or
any open provider; the input is a `GenusZeroLocalMontelChartPatch` plus a source
chart modeled as an `OpenPartialHomeomorph X ℂ`.

## The source chart as an `OpenPartialHomeomorph X ℂ`

The honest data X's atlas supplies around the patch point is a partial
homeomorphism `φ : OpenPartialHomeomorph X ℂ` (the chart at the point,
restricted to the realizing neighborhood).  We set

* `source      := φ.source`,
* `sourceChart := (φ : X → ℂ)`,
* `sourceSection := (φ.symm : ℂ → X)`,

and every constructor hypothesis is read off `φ`'s homeomorphism laws
(`OpenPartialHomeomorph.left_inv`, `right_inv`, `open_source`) together with the
chart-ball normalization field `domainRadius_lt_chart`.  The three input
hypotheses are exactly what the construction genuinely provides:

* `hφ_smooth`  — the source chart is a smooth coordinate on its source;
* `himage`     — the source chart lands inside the chart-ball *domain* ball;
* `hsymm_image`— the inverse-function-theorem inverse values of the chart-ball
  land in `φ`'s image (so `φ.symm` is a genuine right inverse there).

This is pure packaging plus local chart topology: no new analytic content, hence
no `sorry`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**Source-chart package, per chart-ball datum.**

Given a `GenusZeroLocalMontelChartPatch` and a source chart
`φ : OpenPartialHomeomorph X ℂ` realizing its chart-ball coordinate (smooth on
its source, landing in the chart-ball domain ball, with the chart-ball
inverse-function-theorem inverse values lying in `φ`'s image), produce a source
set, source chart and local section satisfying **all** the hypotheses of
`montelRealizedPatch_of_sourceChartLocalSection`.

The construction instantiates this once per selected patch to obtain a
`MontelRealizedPatch` by a single application of the local-section constructor
(see `exists_montelRealizedPatch_of_chartBallData`).
-/
theorem exists_sourceChartPackage_of_chartBallData
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) φ φ.source)
    (himage :
      ∀ x, x ∈ φ.source →
        φ x ∈
          Metric.ball localPatch.chartBall.center
            localPatch.localChart.domainRadius)
    (hsymm_image :
      ∀ z,
        z ∈ localPatch.targetChart.target ∨
          z ∈ localPatch.localChart.localOpen.target →
        localPatch.localChart.localOpen.symm z ∈ φ.target) :
    ∃ (source : Set X) (sourceChart : X → ℂ) (sourceSection : ℂ → X),
      IsOpen source ∧
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) sourceChart source ∧
      (∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center
            (localPatch.chartBall.radius : ℝ)) ∧
      (∀ x, x ∈ source →
        sourceChart x ∈
          Metric.ball localPatch.chartBall.center
            localPatch.localChart.domainRadius) ∧
      (∀ z,
        z ∈ localPatch.targetChart.target ∨
          z ∈ localPatch.localChart.localOpen.target →
        sourceChart (sourceSection (localPatch.localChart.localOpen.symm z)) =
          localPatch.localChart.localOpen.symm z) ∧
      (∀ x, x ∈ source → sourceSection (sourceChart x) = x) := by
  refine ⟨φ.source, (φ : X → ℂ), (φ.symm : ℂ → X), φ.open_source, hφ_smooth,
    ?_, himage, ?_, ?_⟩
  · -- chart lands in the radius ball: domain ball ⊆ radius ball.
    intro x hx
    exact Metric.ball_subset_ball
      (le_of_lt localPatch.localChart.domainRadius_lt_chart) (himage x hx)
  · -- section right inverse on the relevant target values.
    intro z hz
    exact φ.right_inv (hsymm_image z hz)
  · -- section left inverse on the source.
    intro x hx
    exact φ.left_inv hx

/--
**Realized-patch corollary, per chart-ball datum.**

Compose `exists_sourceChartPackage_of_chartBallData` with the local-section
constructor `montelRealizedPatch_of_sourceChartLocalSection` to obtain a
`MontelRealizedPatch X localPatch` directly.  This is the one-call form the
global construction invokes per selected patch.
-/
theorem exists_montelRealizedPatch_of_chartBallData
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) φ φ.source)
    (himage :
      ∀ x, x ∈ φ.source →
        φ x ∈
          Metric.ball localPatch.chartBall.center
            localPatch.localChart.domainRadius)
    (hsymm_image :
      ∀ z,
        z ∈ localPatch.targetChart.target ∨
          z ∈ localPatch.localChart.localOpen.target →
        localPatch.localChart.localOpen.symm z ∈ φ.target) :
    Nonempty (MontelRealizedPatch X localPatch) := by
  obtain ⟨source, sourceChart, sourceSection, hopen, hsmooth, hball, hdomain,
    hright, hleft⟩ :=
    exists_sourceChartPackage_of_chartBallData localPatch φ hφ_smooth himage
      hsymm_image
  exact ⟨montelRealizedPatch_of_sourceChartLocalSection localPatch source hopen
    sourceChart sourceSection hsmooth hball hdomain hright hleft⟩

end JacobianChallenge.HolomorphicForms
