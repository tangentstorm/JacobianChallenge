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

/-!
## M-E — indexed family form of the raw-chart realized-patch corollary

The engine's consumption boundary
(`genusZero_stage_engine_payload`, and the `…with_local_realizations` provider in
`GenusZeroUniformization.lean`) does not consume one realized patch — it consumes
a **materialized indexed family**
`realizedPatch : ∀ i, MontelRealizedPatch X (localPatch i)` over its patch index.
`exists_montelRealizedPatch_of_rawChart` produces only the single-patch
`Nonempty (MontelRealizedPatch X localPatch)`.

The family form below closes that last gap: from a per-index family of raw charts
`φ i` with the per-index M-D hypotheses, it produces the materialized pi-type
`Nonempty (∀ i, MontelRealizedPatch X (localPatch i))`.  Since
`MontelRealizedPatch` is *data*, materializing the family choices through each
pointwise `Nonempty` (`Classical.choice` per index — no `Fintype`/`Nonempty ι`
is consumed by the choice, so we state it at full generality `ι : Type*` and let
the engine instantiate at its `Fintype`-indexed `PatchIndex`).
-/

/--
**Raw-source-chart realized-patch family** (M-E).

Indexed family form of `exists_montelRealizedPatch_of_rawChart`: from a family of
raw atlas charts `φ i`, each with the M-D hypotheses for `localPatch i`, produce
the materialized family `∀ i, MontelRealizedPatch X (localPatch i)`.  This is the
shape the engine's final-edge payload consumes (one `MontelRealizedPatch` per
patch index, materialized, not merely nonempty).

Stated at full generality in the index type `ι : Type*` — no `Fintype` or
`Nonempty ι` is used, the materialization is pointwise `Classical.choice`; the
engine instantiates `ι` at its `Fintype`-indexed `PatchIndex`. -/
theorem exists_montelRealizedPatch_family_of_rawChart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {ι : Type*}
    (localPatch : ι → GenusZeroLocalMontelChartPatch)
    (φ : ι → OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (⊤ : WithTop ℕ∞) (φ i) (φ i).source)
    (hsymm_image :
      ∀ i z,
        z ∈ (localPatch i).targetChart.target ∨
          z ∈ (localPatch i).localChart.localOpen.target →
        (localPatch i).localChart.localOpen.symm z ∈ (φ i).target) :
    Nonempty (∀ i, MontelRealizedPatch X (localPatch i)) := by
  -- Each index gives a nonempty realized patch by the single-patch M-D corollary.
  have hpt : ∀ i, Nonempty (MontelRealizedPatch X (localPatch i)) := fun i =>
    exists_montelRealizedPatch_of_rawChart (localPatch i) (φ i) (hφ_smooth i)
      (hsymm_image i)
  -- Materialize the family by choosing through each pointwise `Nonempty`.
  exact ⟨fun i => (hpt i).some⟩

/-!
## M-F — packaging adapter for the realized-patch finite-cover existential

The engine's selection target
`genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches`
(`GenusZeroUniformization.lean`) owes three things: choose the normalized
chart-ball limits [engine spine], build realized Montel patch bundles for those
local coordinates [M-D/M-E, above], and prove the two-chart assignment while
packaging the existential.  This last packaging step is pure assembly, but doing
it from `Nonempty.some` is awkward: the engine wants to control the concrete
`realizedPatch` witness it proves the bookkeeping about.

`exists_realizedPatchCover_of_components` is that green seam: it takes the
realized family as an **explicit** argument (the engine's chosen witness) plus the
cover / target-cover / `targetChart`-agreement / two-chart bookkeeping stated
about it, and assembles the exact existential conclusion of the selection target.
With it, the engine's remaining proof reduces to: build the components (raw
charts via M-E, normalized limits, the two-chart facts) and
`exact exists_realizedPatchCover_of_components …`.  No analytic content — pure
existential repackaging; it consumes the spine's outputs as hypotheses and
asserts nothing about the construction, so it is not gated on the open spine.
-/

universe u

/--
**Realized-patch finite-cover packaging adapter** (M-F).

Assemble the existential conclusion of
`genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches` from an
explicit realized patch family and its bookkeeping facts.  The hypotheses mirror
the four conjuncts of that conclusion verbatim:

* `hsource_cover` — the realized patch sources cover `X`;
* `htarget_cover` — every `OnePoint ℂ` value is hit by some patch target chart;
* `htarget_eq` — each local patch's `targetChart` agrees with its realization's;
* the two-chart clause — identity/inversion indices, the exhaustive alternative,
  and the two normalized-chart-ball-limit nonemptiness facts.

Stated at full generality in `ι : Type*` (the engine instantiates it at its
`Fintype`-indexed `PatchIndex`); this is the green callee the engine `exact`s to
discharge the packaging half of its selection `sorry`. -/
theorem exists_realizedPatchCover_of_components
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (localPatch : ι → GenusZeroLocalMontelChartPatch)
    (realizedPatch : ∀ i, MontelRealizedPatch X (localPatch i))
    (hsource_cover : ∀ x : X, ∃ i : ι, x ∈ (realizedPatch i).patch.source)
    (htarget_cover :
      ∀ y : OnePoint ℂ, ∃ (i : ι) (z : ℂ),
        z ∈ (realizedPatch i).patch.targetChart.target ∧
          y = (realizedPatch i).patch.targetChart.symm z)
    (htarget_eq :
      ∀ i, (localPatch i).targetChart = (realizedPatch i).patch.targetChart)
    (htwo_chart :
      ∃ identityIndex inversionIndex : ι,
        (realizedPatch identityIndex).patch.targetChart = identityChart ∧
        (realizedPatch inversionIndex).patch.targetChart = inversionChart ∧
        (∀ i, i = identityIndex ∨ i = inversionIndex) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch identityIndex).chartBall.center 0 1
          (localPatch identityIndex).chartBall.radius
          (localPatch identityIndex).chartBall.toFun) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch inversionIndex).chartBall.center 0 1
          (localPatch inversionIndex).chartBall.radius
          (localPatch inversionIndex).chartBall.toFun)) :
    ∃ (PatchIndex : Type u) (_ : Fintype PatchIndex) (_ : Nonempty PatchIndex)
      (localPatch : PatchIndex → GenusZeroLocalMontelChartPatch)
      (realizedPatch : ∀ i, MontelRealizedPatch X (localPatch i)),
      (∀ x : X, ∃ i : PatchIndex, x ∈ (realizedPatch i).patch.source) ∧
      (∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
        z ∈ (realizedPatch i).patch.targetChart.target ∧
          y = (realizedPatch i).patch.targetChart.symm z) ∧
      (∀ i, (localPatch i).targetChart = (realizedPatch i).patch.targetChart) ∧
      (∃ identityIndex inversionIndex : PatchIndex,
        (realizedPatch identityIndex).patch.targetChart = identityChart ∧
        (realizedPatch inversionIndex).patch.targetChart = inversionChart ∧
        (∀ i, i = identityIndex ∨ i = inversionIndex) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch identityIndex).chartBall.center 0 1
          (localPatch identityIndex).chartBall.radius
          (localPatch identityIndex).chartBall.toFun) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch inversionIndex).chartBall.center 0 1
          (localPatch inversionIndex).chartBall.radius
          (localPatch inversionIndex).chartBall.toFun)) :=
  ⟨ι, inferInstance, inferInstance, localPatch, realizedPatch, hsource_cover,
    htarget_cover, htarget_eq, htwo_chart⟩

/-!
## M-G — one-call per-patch realization over `ofChartBallLimit`

This is the green seam just *upstream* of M-D.  Per patch, the engine produces a
normalized chart-ball limit, promotes it to a
`ChartBallPowerSeries.LocalNormalizedChartHomeomorphData` (F2 green leaf
`exists_localNormalizedChartHomeomorphData_of_tendstoLocallyUniformlyOn`), and
assembles a `GenusZeroLocalMontelChartPatch` via
`GenusZeroLocalMontelChartPatch.ofChartBallLimit`; only then does it realize the
patch.  `exists_montelRealizedPatch_ofChartBallLimit` composes the
`ofChartBallLimit` assembly with the M-D corollary into one call.

Following the M-F design lesson, the local-chart datum and the raw source chart
are taken **explicitly** so the engine controls the concrete witnesses it states
the M-D `hsymm_image` hypothesis against.  Because `ofChartBallLimit` sets its
fields definitionally, `(ofChartBallLimit chartBall localChart …).localChart`
reduces to `localChart` (and `.chartBall` to `chartBall`), so the M-D hypotheses
are stated against the concrete `localChart` the caller holds and transfer by
`rfl` — no restatement.  No new analytic content; not gated on the open spine
(the normalized-limit data is an input). -/

/--
**One-call per-patch realization over `ofChartBallLimit`** (M-G).

Given the data assembling a `GenusZeroLocalMontelChartPatch` from a normalized
chart-ball limit — a `ChartBallPowerSeries`, its
`LocalNormalizedChartHomeomorphData`, a standard target chart — together with a
raw source chart `φ` satisfying the M-D hypotheses for the assembled patch,
produce a `MontelRealizedPatch` for that patch in one call.  Composes
`GenusZeroLocalMontelChartPatch.ofChartBallLimit` with
`exists_montelRealizedPatch_of_rawChart` (M-D); the `ofChartBallLimit`
projections are definitional, so the hypotheses match by `rfl`. -/
theorem exists_montelRealizedPatch_ofChartBallLimit
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (chartBall : ChartBallPowerSeries)
    (localChart : chartBall.LocalNormalizedChartHomeomorphData)
    (targetChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (hstd : targetChart = identityChart ∨ targetChart = inversionChart)
    (φ : OpenPartialHomeomorph X ℂ)
    (hφ_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) φ φ.source)
    (hsymm_image :
      ∀ z,
        z ∈ targetChart.target ∨ z ∈ localChart.localOpen.target →
        localChart.localOpen.symm z ∈ φ.target) :
    Nonempty
      (MontelRealizedPatch X
        (GenusZeroLocalMontelChartPatch.ofChartBallLimit chartBall localChart
          targetChart hstd)) :=
  exists_montelRealizedPatch_of_rawChart
    (GenusZeroLocalMontelChartPatch.ofChartBallLimit chartBall localChart
      targetChart hstd)
    φ hφ_smooth hsymm_image

/-!
## M-H — `Bool`-indexed two-chart specialization of the cover-packaging adapter

The genus-zero finite cover is *always* exactly two charts: one realizing the
identity target chart, one the inversion chart.  The selection-target conclusion
carries the exhaustive alternative `∀ i, i = identityIndex ∨ i = inversionIndex`.
The general `exists_realizedPatchCover_of_components` is stated over an arbitrary
`Fintype ι`, so a caller with exactly two patches must still package them into a
`Fintype` family and discharge the exhaustive alternative by hand.

`exists_realizedPatchCover_of_twoCharts` specializes to `PatchIndex := Bool`:
it takes the two realized patches explicitly (identity at `false`, inversion at
`true`) together with the two-patch-shaped bookkeeping, and synthesizes the
`Fintype`/`Nonempty` instances, the exhaustive alternative (`Bool.rec`), and the
source/target cover from the two-patch disjunctions — producing the same
selection-target existential.  Non-opaque (the patches are explicit, as in M-F)
and non-gated; pure assembly. -/

/--
**Two-chart cover packaging** (M-H).

`Bool`-indexed specialization of `exists_realizedPatchCover_of_components` to the
genus-zero two-chart structure: from the identity and inversion realized patches
and their two-patch bookkeeping, assemble the selection-target existential with
`PatchIndex := Bool`.  The `Fintype`/`Nonempty`/exhaustive-alternative clauses are
synthesized for free. -/
theorem exists_realizedPatchCover_of_twoCharts
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (idPatch inversionPatch : GenusZeroLocalMontelChartPatch)
    (realizedId : MontelRealizedPatch X idPatch)
    (realizedInv : MontelRealizedPatch X inversionPatch)
    (hsource_cover :
      ∀ x : X,
        x ∈ realizedId.patch.source ∨ x ∈ realizedInv.patch.source)
    (htarget_cover :
      ∀ y : OnePoint ℂ,
        (∃ z : ℂ, z ∈ realizedId.patch.targetChart.target ∧
            y = realizedId.patch.targetChart.symm z) ∨
          (∃ z : ℂ, z ∈ realizedInv.patch.targetChart.target ∧
            y = realizedInv.patch.targetChart.symm z))
    (htarget_eq_id : idPatch.targetChart = realizedId.patch.targetChart)
    (htarget_eq_inv :
      inversionPatch.targetChart = realizedInv.patch.targetChart)
    (hid_std : realizedId.patch.targetChart = identityChart)
    (hinv_std : realizedInv.patch.targetChart = inversionChart)
    (hid_limit :
      Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
        idPatch.chartBall.center 0 1 idPatch.chartBall.radius
        idPatch.chartBall.toFun))
    (hinv_limit :
      Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
        inversionPatch.chartBall.center 0 1 inversionPatch.chartBall.radius
        inversionPatch.chartBall.toFun)) :
    ∃ (PatchIndex : Type) (_ : Fintype PatchIndex) (_ : Nonempty PatchIndex)
      (localPatch : PatchIndex → GenusZeroLocalMontelChartPatch)
      (realizedPatch : ∀ i, MontelRealizedPatch X (localPatch i)),
      (∀ x : X, ∃ i : PatchIndex, x ∈ (realizedPatch i).patch.source) ∧
      (∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
        z ∈ (realizedPatch i).patch.targetChart.target ∧
          y = (realizedPatch i).patch.targetChart.symm z) ∧
      (∀ i, (localPatch i).targetChart = (realizedPatch i).patch.targetChart) ∧
      (∃ identityIndex inversionIndex : PatchIndex,
        (realizedPatch identityIndex).patch.targetChart = identityChart ∧
        (realizedPatch inversionIndex).patch.targetChart = inversionChart ∧
        (∀ i, i = identityIndex ∨ i = inversionIndex) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch identityIndex).chartBall.center 0 1
          (localPatch identityIndex).chartBall.radius
          (localPatch identityIndex).chartBall.toFun) ∧
        Nonempty (ChartBallPowerSeries.NormalizedChartBallLimit
          (localPatch inversionIndex).chartBall.center 0 1
          (localPatch inversionIndex).chartBall.radius
          (localPatch inversionIndex).chartBall.toFun)) := by
  -- `false ↦ identity`, `true ↦ inversion`.
  refine ⟨Bool, inferInstance, inferInstance,
    fun b => bif b then inversionPatch else idPatch,
    fun b => by cases b with
      | false => exact realizedId
      | true => exact realizedInv, ?_, ?_, ?_, ?_⟩
  · -- source cover
    intro x
    rcases hsource_cover x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  · -- target cover
    intro y
    rcases htarget_cover y with ⟨z, hz, hy⟩ | ⟨z, hz, hy⟩
    · exact ⟨false, z, hz, hy⟩
    · exact ⟨true, z, hz, hy⟩
  · -- per-index targetChart agreement
    intro b
    cases b with
    | false => exact htarget_eq_id
    | true => exact htarget_eq_inv
  · -- two-chart clause: identityIndex := false, inversionIndex := true
    refine ⟨false, true, hid_std, hinv_std, ?_, hid_limit, hinv_limit⟩
    intro b
    cases b with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-!
## M-I — chart-ball-domain → patch-source coordinate convergence transfer

The green E→F seam.  The engine's diagonal extraction produces, per patch,
locally-uniform convergence of the chart-ball readings on the chart-ball domain
`Metric.ball center radius` (in `ℂ`).  The selection-target `F` clause instead
needs locally-uniform convergence of the patch *coordinate* on `patch.source`
(in `X`).  The bridge is a pullback of the `ℂ`-domain convergence along the
realized patch's `sourceChart`, using only the realization fields the
`MontelRealizedPatch` already carries:

* `sourceChart` is continuous on `patch.source`
  (`sourceChart_contMDiffOn.continuousOn`);
* `sourceChart` maps `patch.source` into `ball center radius`
  (`sourceChart_mem_chartBall`), giving the `MapsTo` for the precomposition;
* `coord_eq_chartBall` rewrites the pulled-back limit
  `chartBall.toFun ∘ sourceChart` to `patch.coord` on the source.

`Mathlib.TendstoLocallyUniformlyOn.comp` does the precomposition; the limit is
rewritten by `congr_right` on the source `EqOn`.  No analytic content; not gated
on the open spine — the chart-ball convergence is a hypothesis. -/

/--
**Coordinate convergence transfer** (M-I).

Pull back chart-ball-domain locally-uniform convergence to patch-source
locally-uniform convergence of the patch coordinate.  Given a realized patch and
a family `g : ℕ → ℂ → ℂ` converging locally uniformly to
`localPatch.chartBall.toFun` on the chart-ball domain, the precomposition
`fun n x => g n (rp.realization.sourceChart x)` converges locally uniformly to
`rp.patch.coord` on `rp.patch.source`. -/
theorem tendstoLocallyUniformlyOn_coord_of_chartBall
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {localPatch : GenusZeroLocalMontelChartPatch}
    (rp : MontelRealizedPatch X localPatch)
    (g : ℕ → ℂ → ℂ)
    (hg :
      TendstoLocallyUniformlyOn (fun n z => g n z) localPatch.chartBall.toFun
        Filter.atTop
        (Metric.ball localPatch.chartBall.center
          (localPatch.chartBall.radius : ℝ))) :
    TendstoLocallyUniformlyOn
      (fun n x => g n (rp.realization.sourceChart x)) rp.patch.coord
      Filter.atTop rp.patch.source := by
  -- Precompose the chart-ball convergence with `sourceChart : source → ball`.
  have hmaps :
      Set.MapsTo rp.realization.sourceChart rp.patch.source
        (Metric.ball localPatch.chartBall.center
          (localPatch.chartBall.radius : ℝ)) :=
    fun x hx => rp.realization.sourceChart_mem_chartBall x hx
  have hcont :
      ContinuousOn rp.realization.sourceChart rp.patch.source :=
    rp.realization.sourceChart_contMDiffOn.continuousOn
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun n => g n ∘ rp.realization.sourceChart)
        (localPatch.chartBall.toFun ∘ rp.realization.sourceChart)
        Filter.atTop rp.patch.source :=
    hg.comp rp.realization.sourceChart hmaps hcont
  -- Rewrite the limit `chartBall.toFun ∘ sourceChart = coord` on the source.
  refine hcomp.congr_right ?_
  intro x hx
  exact (rp.realization.coord_eq_chartBall x hx).symm

end JacobianChallenge.HolomorphicForms
