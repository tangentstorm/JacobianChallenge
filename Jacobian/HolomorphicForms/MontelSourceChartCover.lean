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

/-!
## M-D — domain-ball-restriction convenience form

The two providers above take `himage` — the proof that the source chart lands in
the chart-ball *domain* ball — as an explicit hypothesis.  At the engine's
instantiation point this is a nuisance: the raw atlas chart `φ` is honest, but
proving `himage` on *all* of `φ.source` forces the caller to have already shrunk
`φ` to the domain-ball preimage.  We do that shrink here, once, with
`OpenPartialHomeomorph.restrOpen`, so that `himage` self-discharges by
construction.

Set `s := φ.source ∩ φ ⁻¹' (Metric.ball center domainRadius)`, which is open by
`φ.isOpen_inter_preimage`, and restrict `φ` to it: `ψ := φ.restrOpen s _`.  Then

* `ψ.source = φ.source ∩ s`, so every `x ∈ ψ.source` has `φ x` in the domain
  ball — `himage` for `ψ` holds by membership unfolding;
* `⇑ψ = ⇑φ` and `⇑ψ.symm = ⇑φ.symm` definitionally (`coe_restrOpen`,
  `coe_restrOpen_symm`), so smoothness transfers by `ContMDiffOn.mono` and the
  section laws transfer verbatim.

**Honesty note on `hsymm_image`.**  One might fear that restricting `φ` forces a
*stronger* inverse-branch hypothesis: the restricted target is genuinely smaller,
`ψ.target = φ.target ∩ φ.symm ⁻¹' s`, so a membership `localOpen.symm z ∈ ψ.target`
would also demand `localOpen.symm z ∈ Metric.ball center domainRadius`.  But the
package conclusion never asks for that: its right-inverse clause is stated about
the section `ψ.symm = φ.symm` applied *directly* to `localOpen.symm z`, and
`φ.right_inv` discharges it from `localOpen.symm z ∈ φ.target` alone — the
restriction shrank the `source`, but the section is still `φ.symm` evaluated at
the same values, so it never touches `ψ.target`.  Consequently the convenience
form is *strictly weaker* in hypotheses than the chart-ball form: it **drops**
`himage` entirely (self-discharged by the restriction) and keeps only the
original `hsymm_image`.  No `hsymm_ball` analogue is owed.
-/

/-- The open set the raw source chart is restricted to: the part of `φ.source`
whose `φ`-image lies in the chart-ball domain ball.  Openness is
`φ.isOpen_inter_preimage` applied to the (open) metric ball. -/
private def rawChartRestrictSet
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ) : Set X :=
  φ.source ∩
    φ ⁻¹' Metric.ball localPatch.chartBall.center localPatch.localChart.domainRadius

/-- The restriction of a raw source chart `φ` to `rawChartRestrictSet`, via
`OpenPartialHomeomorph.restrOpen`.  Its coercion and inverse agree with `φ`
definitionally (`coe_restrOpen`, `coe_restrOpen_symm`). -/
private noncomputable def rawChartRestrict
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ) : OpenPartialHomeomorph X ℂ :=
  φ.restrOpen (rawChartRestrictSet localPatch φ)
    (φ.isOpen_inter_preimage Metric.isOpen_ball)

/--
**Raw-source-chart package form** (M-D).

Same conclusion as `exists_sourceChartPackage_of_chartBallData`, but the
all-of-source `himage` hypothesis is GONE: we restrict `φ` to the domain-ball
preimage with `rawChartRestrict`, where it self-discharges by construction.  What
remains genuinely owed:

* `hφ_smooth` — `φ` is a smooth coordinate on its source (transferred to the
  restricted source by `ContMDiffOn.mono`);
* `hsymm_image` — `localOpen.symm z` lands in `φ.target` (the original fact; the
  section is still `φ.symm`, so no restricted-target analogue is owed — see the
  section docstring).

The produced `source` is the restricted source `(rawChartRestrict …).source`,
i.e. `φ.source ∩ φ ⁻¹' (ball center domainRadius)`. -/
theorem exists_sourceChartPackage_of_rawChart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) φ φ.source)
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
  set ψ := rawChartRestrict localPatch φ with hψ
  -- The restricted source is `φ.source ∩ φ ⁻¹' (ball center domainRadius)`.
  have hψ_source : ψ.source = rawChartRestrictSet localPatch φ := by
    rw [hψ, rawChartRestrict, φ.restrOpen_source]
    exact Set.inter_eq_self_of_subset_right Set.inter_subset_left
  -- Source membership unfolds to `φ.source` membership plus domain-ball image.
  have hmem : ∀ x, x ∈ ψ.source →
      x ∈ φ.source ∧
        φ x ∈
          Metric.ball localPatch.chartBall.center
            localPatch.localChart.domainRadius := by
    intro x hx
    rw [hψ_source, rawChartRestrictSet] at hx
    exact ⟨hx.1, hx.2⟩
  refine ⟨ψ.source, (ψ : X → ℂ), (ψ.symm : ℂ → X), ψ.open_source, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- Smoothness on the smaller source, by restriction and `coe_restrOpen`.
    have hsub : ψ.source ⊆ φ.source := by
      rw [hψ_source, rawChartRestrictSet]; exact Set.inter_subset_left
    rw [hψ, rawChartRestrict, φ.coe_restrOpen]
    exact hφ_smooth.mono hsub
  · -- Chart lands in the radius ball: domain ball ⊆ radius ball.
    intro x hx
    rw [hψ, rawChartRestrict, φ.coe_restrOpen]
    exact Metric.ball_subset_ball
      (le_of_lt localPatch.localChart.domainRadius_lt_chart) (hmem x hx).2
  · -- Chart lands in the domain ball: `himage` self-discharges by construction.
    intro x hx
    rw [hψ, rawChartRestrict, φ.coe_restrOpen]
    exact (hmem x hx).2
  · -- Section right inverse: the section is still `φ.symm`, so `φ.right_inv`
    -- needs only `localOpen.symm z ∈ φ.target` (no restricted-target fact).
    intro z hz
    rw [hψ, rawChartRestrict, φ.coe_restrOpen, φ.coe_restrOpen_symm]
    exact φ.right_inv (hsymm_image z hz)
  · -- Section left inverse on the (restricted) source.
    intro x hx
    rw [hψ, rawChartRestrict, φ.coe_restrOpen, φ.coe_restrOpen_symm]
    exact φ.left_inv (hmem x hx).1

/--
**Raw-source-chart realized-patch corollary** (M-D).

The one-call form over the restriction: compose
`exists_sourceChartPackage_of_rawChart` with the local-section constructor
`montelRealizedPatch_of_sourceChartLocalSection` to obtain a
`MontelRealizedPatch X localPatch` from a raw atlas chart `φ`, with the
all-of-source `himage` hypothesis discharged by the domain-ball restriction. -/
theorem exists_montelRealizedPatch_of_rawChart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (localPatch : GenusZeroLocalMontelChartPatch)
    (φ : OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) φ φ.source)
    (hsymm_image :
      ∀ z,
        z ∈ localPatch.targetChart.target ∨
          z ∈ localPatch.localChart.localOpen.target →
        localPatch.localChart.localOpen.symm z ∈ φ.target) :
    Nonempty (MontelRealizedPatch X localPatch) := by
  obtain ⟨source, sourceChart, sourceSection, hopen, hsmooth, hball, hdomain,
    hright, hleft⟩ :=
    exists_sourceChartPackage_of_rawChart localPatch φ hφ_smooth hsymm_image
  exact ⟨montelRealizedPatch_of_sourceChartLocalSection localPatch source hopen
    sourceChart sourceSection hsmooth hball hdomain hright hleft⟩

end JacobianChallenge.HolomorphicForms
