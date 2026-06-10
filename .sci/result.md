# Phase 0: construct-first paper proof of the Montel providers

## Targets

This proof plan targets exactly the two current Path A provider sorries:

```lean
genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches
genusZeroMontel_finite_cover_coord_representation_with_realized_patches
```

Both are in `Jacobian/HolomorphicForms/GenusZeroUniformization.lean`.  They have
no dedicated blueprint lemma labels yet; the closest blueprint subtree is the
Montel coordinate-representation subtree
`sec:montel-coord-represents`, especially
`lem:montel-selector-coord-represents-uniformization`,
`lem:montel-selector-normal-limit-agrees-with-uniformization`, and
`lem:montel-selector-overlap-compatible-normalized-values`.

The construction must be global-first.  It must not choose unrelated local
limits and later try to cohere them.  The common target sequence is the central
object from which the finite patch family, local chart-ball limits, realized
patches, candidate `u`, and coordinate representation are read off.

## Construct-first proof

### 1. Build one global approximating sequence

Start from the given topological homeomorphism

```lean
_e : X ≃ₜ OnePoint ℂ
```

and build a single sequence

```lean
F : ℕ → X → OnePoint ℂ
```

of finite-stage approximating maps.  Each `F n` is read in either public
`OnePoint ℂ` chart by composing with `identityChart` or `inversionChart`.
Locally, after choosing a source chart on `X`, the chart-reading is packaged as
a `ChartBallPowerSeries`.

Support status:

- Blueprint: the global sequence is implicit in
  `lem:montel-selector-local-limit-tied-to-global-homeomorphism` and
  `lem:montel-selector-normalized-transition-agreement`, but there is no
  construct-first blueprint node for it.
- Lean: no existing declaration constructs this `F` from `_e`.
- Status: new analytic work.  This is the first hard missing theorem.

The local chart-ball analytic substrate for individual chart readings already
exists:

- Blueprint: formalization note in `sec:uniformization-lite-iter3`, local
  chart-ball power series and normal-family extraction bullets.
- Lean: `ChartBallPowerSeries`,
  `ChartBallPowerSeries.ofDiffContOnCl`,
  `ChartBallPowerSeries.hasFPowerSeriesOnBall_of_diffContOnCl`,
  `ChartBallPowerSeries.tendstoLocallyUniformlyOn_partialSum`,
  `ChartBallPowerSeries.tendstoUniformlyOn_partialSum_of_lt`.
- Status: green/sorry-free local substrate.

What is missing at this step is not local power-series packaging; it is the
global construction which turns `_e` into one sequence whose two chart readings
feed all selected patches simultaneously.

### 2. Extract finite normalized chart-ball limits from the same sequence

Choose the finite public target-chart index type with two indices,
corresponding to `identityChart` and `inversionChart`.  On each selected source
neighborhood, apply the chart reading of the same `F` to obtain a normal family
of chart-ball functions.  Use Montel/Arzela-Ascoli extraction and diagonal
subsequence selection to get a common subsequence, still denoted `F`, such that
each chart-reading converges locally uniformly on its selected source patch:

```lean
TendstoLocallyUniformlyOn
  (fun n x => (realizedPatch i).patch.targetChart (F n x))
  (realizedPatch i).patch.coord Filter.atTop
  (realizedPatch i).patch.source
```

Local support that already exists:

- Blueprint: local Montel extraction bullet in the formalization note;
  no precise construct-first node.
- Lean:
  `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`,
  `ChartBallPowerSeries.isCompact_closure_boundedContinuousOnClosedBall_range`,
  `ChartBallPowerSeries.exists_tendsto_subseq_boundedContinuousOnClosedBall`,
  `ChartBallPowerSeries.tendstoUniformlyOn_of_tendsto_boundedContinuousOnClosedBall`,
  `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`.
- Status: green/sorry-free local closed-ball Montel substrate.

Normalization support that already exists:

- Blueprint: local chart-ball and inverse-function bullets in the same
  formalization note.
- Lean:
  `ChartBallPowerSeries.differentiableOn_limit_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.tendstoLocallyUniformlyOn_deriv_of_chartBall_limit`,
  `ChartBallPowerSeries.limit_apply_center_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.deriv_limit_center_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.deriv_limit_center_ne_zero_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.NormalizedChartBallLimit`,
  `ChartBallPowerSeries.normalizedChartBallLimit_of_tendstoLocallyUniformlyOn`.
- Status: green/sorry-free local normalization substrate.

Local inverse-function support that already exists:

- Blueprint: inverse-function local chart bullet in the formalization note.
- Lean:
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData`,
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit`,
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_tendstoLocallyUniformlyOn`.
- Status: green/sorry-free local inverse-function substrate.

Missing global support:

- A real finite-cover theorem that chooses chart balls whose strict closed
  subballs cover `X`, with the common sequence restricted to each.
- A real diagonal extraction theorem for a finite family of chart readings,
  preserving one subsequence for all selected patches.
- A real globally compatible conversion from closed-ball convergence in source
  coordinates to `TendstoLocallyUniformlyOn` on the corresponding patch source.

The six declarations
`chart_local_equicontinuous`, `chart_local_arzela_ascoli`,
`global_totally_bounded_via_chart_cover`, `lebesgue_number_chart_cover`,
`chart_diagonal_extraction`, and `global_sup_via_chart_max` in
`CompactRiemannSurface.lean` are not support here; they are `True` stubs.

### 3. Package local limits as `GenusZeroLocalMontelChartPatch`

For every selected patch index `i`, let `chartBall i` be the chart-ball
power-series limit produced in Step 2.  Its preserved normalization supplies

```lean
ChartBallPowerSeries.NormalizedChartBallLimit
  (chartBall i).center 0 1 (chartBall i).radius (chartBall i).toFun
```

and the inverse-function theorem supplies

```lean
(chartBall i).LocalNormalizedChartHomeomorphData
```

Define

```lean
localPatch i :
  GenusZeroLocalMontelChartPatch
```

using

```lean
GenusZeroLocalMontelChartPatch.ofChartBallLimit
```

with target chart `identityChart` or `inversionChart`.

Support status:

- Blueprint: local chart-ball power-series and inverse-function bullets in
  `sec:uniformization-lite-iter3`.
- Lean:
  `GenusZeroLocalMontelChartPatch`,
  `GenusZeroLocalMontelChartPatch.ofChartBallLimit`,
  `ChartBallPowerSeries.NormalizedChartBallLimit`,
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit`.
- Status: green/sorry-free packaging once Step 2 supplies the limits.

### 4. Build realized patches from source charts and sections

For each `localPatch i`, choose the source set, source coordinate
`sourceChart i : X → ℂ`, and local section `sourceSection i : ℂ → X` coming
from the source chart.  Then build

```lean
realizedPatch i : MontelRealizedPatch X (localPatch i)
```

by the local-section constructor.

Support status:

- Blueprint: `lem:montel-local-patch-realization` for the realization concept;
  `lem:montel-selector-chartball-value-represents-local-coordinate` for the
  coordinate equation it supplies.
- Lean:
  `MontelRealizedPatch`,
  `GenusZeroLocalMontelPatchRealization`,
  `montelRealizedPatch_of_sourceChartLocalSection`,
  `montelRealizedPatch_of_sourceChart`,
  `montelLocalPatchRealization`,
  `montelRealizationPatch_coord_invCoord`,
  `montelRealizationPatch_invCoord_coord`,
  `ChartBallPowerSeries.contMDiffOn_toFun_ball`.
- Status: green/sorry-free realization substrate, assuming the caller supplies
  the honest source chart, section, source membership, and section inverse
  hypotheses.

Missing support:

- A source-chart finite-cover theorem that supplies the actual source sets,
  smooth source charts, local sections, source membership in the selected
  chart balls, and the section left/right inverse hypotheses required by
  `montelRealizedPatch_of_sourceChartLocalSection`.

### 5. Read off the first provider

The first target provider is then a pure payload read:

```lean
genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches
```

Return:

- `PatchIndex`, `Fintype PatchIndex`, and `Nonempty PatchIndex` from the finite
  two-chart cover;
- `localPatch`;
- `realizedPatch`;
- source cover from the finite source-cover construction;
- target cover from the two public charts on `OnePoint ℂ`;
- `(localPatch i).targetChart = (realizedPatch i).patch.targetChart`, which is
  definitional for realized patches built from `localPatch`;
- identity and inversion indices;
- the two normalized limit witnesses from Step 2.

Support status:

- Blueprint: finite-cover/gluing part of `sec:uniformization-lite-iter3`; no
  exact construct-first blueprint node for this exposed provider.
- Lean:
  target provider
  `genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches`
  is open;
  projection wrapper
  `genusZeroMontel_finite_normalized_chartBall_cover_with_local_realizations`
  is green conditional on this provider;
  `onePointCx_identity_or_inversionChart_source` is green/sorry-free for the
  two public chart cover.
- Status: provider remains open because Steps 1, 2, and the source-chart cover
  are missing.

### 6. Define the candidate `u`

Define the candidate global value on a point `x : X` by selecting any patch
`i` containing `x` and setting

```lean
u x = (realizedPatch i).patch.targetChart.symm
        ((realizedPatch i).patch.coord x)
```

The construction is independent of the selected patch because both local
chart readings are limits of the same global sequence `F`.  For same target
charts, uniqueness of the pointwise limit gives equality directly.  For
different target charts, the identity/inversion transition rewrites one chart
reading as the inverse of the other, and uniqueness of limits gives the
transition equality.

Support status:

- Blueprint:
  `lem:montel-selector-overlap-compatible-normalized-values`,
  `lem:montel-selector-normalized-transition-agreement`,
  `lem:global-gluing-overlap-compatible`.
- Lean:
  `genusZeroMontel_normalized_limits_agree_on_overlaps`,
  `genusZeroMontel_overlap_agreement_same_chart`,
  `genusZeroMontel_overlap_agreement_cross_chart`,
  `TendstoLocallyUniformlyOn.tendsto_at`,
  `tendsto_nhds_unique`,
  `eqOn_of_tendstoLocallyUniformlyOn_same`.
- Status: partially open.  The same-chart and cross-chart overlap lemmas are
  present, but `MontelOverlapAgreement.lean` still has two `sorry` helpers:
  `targetChart_inv_eq` and `targetChart_symm_inv_eq`.  The overlap theorem also
  assumes, rather than constructs, overlap preconnectedness and cross-chart
  nonzero coordinate facts.

Missing support:

- Real proofs of the identity/inversion chart transition helper lemmas.
- A theorem supplying preconnectedness of selected source overlaps.
- A theorem proving cross-chart overlap coordinates are nonzero.
- A formal definition/assembly theorem turning the overlap agreement into a
  continuous bijective `u : X ≃ₜ OnePoint ℂ`.

### 7. Read off the common target sequence

The payload

```lean
∃ F : ℕ → X → OnePoint ℂ, ∀ i,
  TendstoLocallyUniformlyOn
    (fun n x => (realizedPatch i).patch.targetChart (F n x))
    (realizedPatch i).patch.coord Filter.atTop
    (realizedPatch i).patch.source
```

is not additional work after Step 2.  It is exactly the global sequence and
finite-family locally-uniform convergence proved there.

Support status:

- Blueprint: this is the construct-first replacement for the open selector
  nodes `lem:montel-selector-local-limit-tied-to-global-homeomorphism` and
  `lem:montel-selector-normalized-transition-agreement`.
- Lean: the payload occurs explicitly in
  `genusZeroMontel_finite_cover_coord_representation_with_realized_patches`.
- Status: open until the global sequence and finite diagonal extraction theorem
  are proved.

### 8. Prove coordinate and inverse-coordinate representation

For every patch and `x` in its source, the coordinate representation is

```lean
(realizedPatch i).patch.targetChart.symm
  ((realizedPatch i).patch.coord x) = u x
```

by the definition of `u` plus overlap independence.  For every `z` in a target
chart, inverse-coordinate representation is

```lean
(realizedPatch i).patch.invCoord z =
  u.symm ((realizedPatch i).patch.targetChart.symm z)
```

using the local right-inverse/left-inverse fields of `MontelRealizedPatch` and
the definition of `u`.

Support status:

- Blueprint:
  `lem:montel-selector-coord-represents-uniformization`,
  `lem:montel-selector-normal-limit-agrees-with-uniformization`,
  `lem:montel-selector-chartball-value-represents-local-coordinate`,
  `lem:montel-selector-normal-limit-equality-bookkeeping`.
- Lean:
  `MontelRealizedPatch.coord_invCoord`,
  `MontelRealizedPatch.invCoord_coord`,
  `genusZeroGlobalGluing_coord_mem_target_on_patch`,
  `OpenPartialHomeomorph.map_target`,
  `OpenPartialHomeomorph.right_inv`,
  `OpenPartialHomeomorph.left_inv`.
- Status: mostly green local algebra after `u` is constructed, but the global
  `u : X ≃ₜ OnePoint ℂ` assembly is still missing.

### 9. Read off the second provider

The second target provider

```lean
genusZeroMontel_finite_cover_coord_representation_with_realized_patches
```

returns all payloads from the first provider, plus:

- `u`;
- the common target sequence from Step 7;
- coordinate representation from Step 8;
- inverse-coordinate representation from Step 8.

Support status:

- Blueprint: same coordinate-representation subtree as Step 8.
- Lean: target provider is open; wrapper
  `genusZeroMontel_finite_cover_coord_representation` is green conditional on
  this provider.
- Status: open until Steps 1, 2, 6, and 8 are formalized.

## NEW ANALYTIC WORK

1. **Global approximating sequence from `_e`.**  Prove a theorem constructing a
   single sequence `F : ℕ → X → OnePoint ℂ` from `_e : X ≃ₜ OnePoint ℂ` whose
   identity-chart and inversion-chart readings are locally holomorphic
   chart-ball families on the selected source neighborhoods.  Proposed shape:
   a provider returning `F`, finite source neighborhoods, source charts, and
   chart-reading `ChartBallPowerSeries` data for each target chart.  This is
   genuinely hard analytic/topological content.

2. **Real finite chart-ball cover.**  Prove that the selected source chart balls
   and target chart assignments form a finite cover of `X`, with strict closed
   subballs available for Montel extraction.  This replaces any temptation to
   cite `lebesgue_number_chart_cover` or `global_sup_via_chart_max`, which are
   only `True` stubs.  This is hard finite-cover analytic topology.

3. **Finite-family diagonal Montel extraction for one common subsequence.**
   Upgrade the green one-closed-ball extraction lemmas to a theorem for the
   finite family of chart readings of the same `F`, producing one subsequence
   whose readings converge locally uniformly on every selected source patch.
   This replaces `chart_diagonal_extraction`; the existing declaration is a
   `True` stub.  This is hard but standard diagonal/compactness work.

4. **Source-coordinate convergence transfer.**  Convert uniform convergence on
   closed balls in source coordinates to
   `TendstoLocallyUniformlyOn` on the corresponding patch source for
   `(fun n x => targetChart (F n x))`.  This is routine but currently not a
   named theorem.

5. **Source chart and local section package.**  Supply, for each selected patch,
   a smooth source chart, an open source set, a local section, source membership
   in the chart ball/domain ball, and the local section inverse hypotheses
   required by `montelRealizedPatch_of_sourceChartLocalSection`.  The local
   realized-patch constructor is green; this provider is the missing caller
   package.  This is mostly packaging plus local chart topology.

6. **Standard chart transition helpers without `sorry`.**  Replace the two open
   helper proofs in `MontelOverlapAgreement.lean`:
   `targetChart_inv_eq` and `targetChart_symm_inv_eq`.  These are routine
   two-chart computations for `identityChart` and `inversionChart`, but they
   are not green yet.

7. **Overlap topological hypotheses.**  Prove that selected source overlaps are
   preconnected where needed, and prove the cross-chart nonzero coordinate
   condition used by `genusZeroMontel_overlap_agreement_cross_chart`.  This is
   genuine topology/atlas work.

8. **Global `u` assembly as a homeomorphism.**  Package the overlap-independent
   local formula into `u : X ≃ₜ OnePoint ℂ`, including continuity, inverse
   formula, and left/right inverse proofs.  The local algebra is green through
   `MontelRealizedPatch.coord_invCoord` and
   `MontelRealizedPatch.invCoord_coord`; the global quotient/gluing assembly is
   not yet a named green theorem.

9. **Provider assembly theorem.**  After items 1-8, add a narrow theorem that
   returns the exact payload of
   `genusZeroMontel_finite_normalized_chartBall_cover_with_realized_patches`
   and
   `genusZeroMontel_finite_cover_coord_representation_with_realized_patches`.
   This should be mostly existential packaging, not additional analysis.

## Explicit non-substrate

The following declarations in
`Jacobian/HolomorphicForms/CompactRiemannSurface.lean` must not be cited as
Montel support until replaced by real theorems:

- `chart_local_equicontinuous`
- `chart_local_arzela_ascoli`
- `global_totally_bounded_via_chart_cover`
- `lebesgue_number_chart_cover`
- `chart_diagonal_extraction`
- `global_sup_via_chart_max`

They currently prove only `True`.
