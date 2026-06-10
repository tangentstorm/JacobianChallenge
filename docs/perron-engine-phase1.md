# Engine Phase 1: Perron/Dirichlet uniformization plan

Tracking: GitHub issue #232, Path A.

This is the Phase 1 architectural plan for the analytic production layer
identified in `docs/montel-phase05-stage-construction.md`.  The green Montel
layer starts after one already has bounded holomorphic chart-ball families.
This document specifies the upstream engine that must produce normalized
holomorphic stage maps on an exhaustion from `_e : X ≃ₜ OnePoint ℂ` and
topological control data.

## Variant Decision

Decision: build a **Perron/Dirichlet harmonic-dipole engine on bordered
exhaustion stages**, then hand the resulting normalized holomorphic stage maps
to the existing Montel machinery.

The engine shape is:

1. Use `_e` only to choose topological control data: two marked points
   corresponding to `0` and `∞`, separating neighborhoods, cuts, and an
   exhaustion by compact bordered/chart-polygon domains `Ω n`.
2. On each cut stage domain, solve a normalized Dirichlet problem for a
   harmonic dipole/log-potential with prescribed singular behavior at the two
   marked ends and controlled boundary values.
3. Construct a harmonic conjugate on the cut stage domain, exponentiate or
   integrate to obtain a single-valued holomorphic coordinate-like stage map.
4. Normalize the resulting stage map at fixed marked source data so the
   sequence cannot collapse under Montel extraction.
5. Extend by a fixed filler outside `Ω n`, and use eventual containment to
   restrict the total sequence to the selected patch sources.

This is a Perron/Dirichlet variant, not a Koebe iteration.  It uses Koebe-style
exhaustion only as the staging framework and uses Montel only for compactness
after stage maps exist.

The two strongest reasons:

- **Correct holomorphicity boundary.**  A tempting alternative is to map
  `_e '' Ω n` as a planar topological domain and pull the map back along `_e`.
  That does not prove holomorphicity on `X`, because `_e` is only a
  homeomorphism.  The analytic stage map must be built from the complex
  structure of `X`; Perron/Dirichlet does that.
- **Best reuse of green work after the hard analytic leaf.**  Once the
  harmonic stage map exists, the rest of the path matches the green substrate:
  `ChartBallPowerSeries.ofDiffContOnCl`,
  `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`,
  `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`,
  normalized-limit packaging, source-chart realization, and finite diagonal
  extraction.

What would force a revisit: if Mathlib's partial Riemann-mapping development
grows into a theorem for Riemann surfaces or a theorem that can be applied to
holomorphic charts with compatible transition data, the stage-map existence
branch should be reconsidered.  The current local theorem is only planar and
does not turn a topological homeomorphism `_e` into holomorphic coordinates.

## Verified Substrate

### Project Declarations

Green terminal consumers after stage maps and bounds exist:

- `ChartBallPowerSeries.ofDiffContOnCl`: packages an open-ball differentiable,
  closed-ball continuous chart reading as a `ChartBallPowerSeries`.
- `ChartBallPowerSeries.hasFPowerSeriesOnBall_of_diffContOnCl` and
  `ChartBallPowerSeries.hasFPowerSeriesOnBall`: local power-series expansion.
- `ChartBallPowerSeries.norm_deriv_le_of_sphere_bound` and
  `ChartBallPowerSeries.norm_image_sub_le_of_cauchy_bound`: Cauchy estimates.
- `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`:
  conditional equicontinuity from uniform Cauchy-circle bounds.
- `ChartBallPowerSeries.boundedContinuousOnClosedBall`,
  `ChartBallPowerSeries.isCompact_closure_boundedContinuousOnClosedBall_range`,
  `ChartBallPowerSeries.exists_tendsto_subseq_boundedContinuousOnClosedBall`,
  `ChartBallPowerSeries.tendstoUniformlyOn_of_tendsto_boundedContinuousOnClosedBall`,
  and `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`:
  local Arzela-Ascoli/Montel extraction.
- `ChartBallPowerSeries.normalizedChartBallLimit_of_tendstoLocallyUniformlyOn`,
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit`,
  and
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_tendstoLocallyUniformlyOn`:
  nonconstant normalized limit and local inverse packaging.
- `exists_subseq_tendstoUniformlyOn_closedBall_finite` and
  `exists_diagonal_subseq_tendstoLocallyUniformlyOn_finite` in
  `MontelDiagonalExtraction.lean`: green finite-family diagonal extraction.
- `exists_sourceChartPackage_of_chartBallData` and
  `exists_montelRealizedPatch_of_chartBallData` in
  `MontelSourceChartCover.lean`, plus
  `montelRealizedPatch_of_sourceChartLocalSection` in
  `MontelLocalPatchRealization.lean`: source-chart realization.
- `genusZeroMontel_normalized_limits_agree_on_overlaps` in
  `MontelOverlapAgreement.lean`: common-sequence overlap agreement.

Local harmonic project work that may be reused but is not a full engine:

- `HasLogarithmicSingularityAtReal.log_abs_at`,
  `HasLogarithmicSingularityAtReal.neg_log_abs_at`,
  `HasLogarithmicSingularityAtReal.dipole_at_pos`,
  `HasLogarithmicSingularityAtReal.dipole_at_neg`, and
  `existence_of_dipole_harmonic_on_complex` in `HarmonicDipole.lean`.
- `IsHarmonicConjugateAtReal.*` lemmas, especially
  `dipole_conjugate_exists_at_off_PQ`,
  `dipole_isHarmonicOffReal_on_complex`,
  `existence_of_dipole_harmonic_off_on_X`,
  and `chart_pullback_dipole_has_conjugate_at_off_PQ` in
  `HarmonicConjugate.lean`.

These are useful chart-local and model-plane ingredients.  They do not solve
Dirichlet problems on bordered stages or supply global periods/single-valued
conjugates.

Explicit non-substrate:

- The `True` declarations in `CompactRiemannSurface.lean`, including
  `chart_local_equicontinuous`, `chart_local_arzela_ascoli`,
  `global_totally_bounded_via_chart_cover`, `lebesgue_number_chart_cover`,
  `chart_diagonal_extraction`, and `global_sup_via_chart_max`, are not used.

### Mathlib Support Verified In The Local Checkout

Useful toward Perron/Dirichlet:

- `HarmonicAt`, `HarmonicOnNhd`, and `harmonicOnNhd_const` in
  `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic`.
- `HarmonicContOnCl` and `HarmonicOnNhd.harmonicContOnCl` in
  `Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl`.
- `ContDiffAt.harmonicAt`, `AnalyticAt.harmonicAt`,
  `AnalyticAt.harmonicAt_re`, `AnalyticAt.harmonicAt_im`, and
  `AnalyticAt.harmonicAt_log_norm` in
  `Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions`.
- `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` and
  `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq` in
  `Mathlib.Analysis.Complex.Harmonic.Analytic`.
- `InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul` and
  `InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul` in
  `Mathlib.Analysis.Complex.Harmonic.Poisson`.
- `poissonKernel` and `DiffContOnCl.circleAverage_poissonKernel_smul` in
  `Mathlib.Analysis.Complex.Poisson`.
- Maximum-modulus principles in `Mathlib.Analysis.Complex.AbsMax`, including
  `Complex.norm_eqOn_closedBall_of_isMaxOn`,
  `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`,
  `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, and
  `Complex.norm_le_of_forall_mem_frontier_norm_le`.
- Cauchy integral and Cauchy derivative infrastructure in
  `Mathlib.Analysis.Complex.CauchyIntegral` and
  `Mathlib.Analysis.Complex.Liouville`.

Useful only as context, not as the chosen engine leaf:

- `Complex.exists_injective_not_dense_image_deriv_ne_zero` and
  `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` in
  `Mathlib.Analysis.Complex.RiemannMapping`.  These are planar-domain
  statements.  They do not apply to `X` through `_e` without already knowing
  conformality.

Negative search results:

- No usable `Subharmonic`/`subharmonic` API was found.
- No general "Dirichlet problem on a disc/domain exists for boundary data"
  theorem was found.  The Poisson files provide representation formulas for
  functions already known to be harmonic/differentiable.
- No Koebe iteration, kernel convergence, or Caratheodory kernel theorem API
  was found.

## Variant Risk Comparison

### Perron/Dirichlet

Worst step: construct the normalized harmonic stage object on each bordered
domain, with boundary control and a single-valued conjugate after cuts.

Risk: hard own-subtree.  This is genuine new potential theory, but its output
is exactly the analytic object the rest of the project can consume.

### Koebe Iteration

Worst step: define an iterative correction scheme over overlapping bordered
charts and prove convergence with shrinking transition defects, preserved
normalization, and compatibility with the finite patch family.

Risk: hard own-subtree, with less usable Mathlib support than Perron/Dirichlet.
It also duplicates part of the normal-family compactness already green in the
project.

### Planar Riemann-Mapping Pullback

Worst step: prove the pullback of a planar map along `_e` is holomorphic.

Risk: invalid/circular with the current input.  `_e` is topological only.  This
variant is rejected unless the input interface changes to provide conformal
stage charts.

## Top-Down Tree

Root target:

`stage_engine_to_genusZeroMontel_finite_cover_coord_representation_with_realized_patches`

Input: `X` with the hypotheses of
`genusZeroMontel_finite_cover_coord_representation_with_realized_patches` and
`_e : X ≃ₜ OnePoint ℂ`.

Output includes exactly:

```lean
∃ F : ℕ → X → OnePoint ℂ, ∀ i,
  TendstoLocallyUniformlyOn
    (fun n x => (realizedPatch i).patch.targetChart (F n x))
    (realizedPatch i).patch.coord Filter.atTop
    (realizedPatch i).patch.source
```

### A. Topological Control And Stage Domains

Status: NEW-WORK, serial spine.

A1. Marked data from `_e`.

- Choose `P∞ P0 : X` with `_e P∞ = ∞` and `_e P0 = 0` or the corresponding
  `OnePoint` values.
- Choose a base normalization point away from both.
- Leaves: `Homeomorph` bijectivity, compact Hausdorff separation, chart
  neighborhoods.
- Classification: routine/multi-commit.

A2. Bordered/chart-polygon exhaustion `Ω n`.

- Required properties: `IsOpen (Ω n)`, monotone, eventually contains each
  selected source patch compactum, avoids temporary cut pieces, and has
  boundary represented by finitely many chart arcs/polygons.
- Classification: hard own-subtree.  This is the main topological stage
  construction.

A3. Cut system on each `Ω n`.

- Choose cuts making `Ωcut n` simply connected enough for a single-valued
  harmonic conjugate.
- Required: cuts avoid selected compact patch balls eventually or have local
  chart subballs that avoid cuts.
- Classification: hard multi-commit, serial with A2.

A4. Eventual containment.

- For every realized patch source and closed coordinate subball used in local
  uniform convergence, prove `∃ N, ∀ n ≥ N, K ⊆ Ωcut n`.
- Classification: routine/multi-commit; farmable after A2/A3 statements.

### B. Harmonic Stage Construction

Status: NEW-WORK, hard analytic spine.

B1. Stage boundary data and dipole singular model.

- Define boundary values and local logarithmic singular models near `P0` and
  `P∞`.
- Existing leaves:
  `HasLogarithmicSingularityAtReal.log_abs_at`,
  `HasLogarithmicSingularityAtReal.neg_log_abs_at`,
  `HasLogarithmicSingularityAtReal.dipole_at_pos`,
  `HasLogarithmicSingularityAtReal.dipole_at_neg`,
  `existence_of_dipole_harmonic_on_complex`.
- Classification: multi-commit hard/routine mix.

B2. Dirichlet/Perron existence on `Ωcut n`.

- New theorem shape:
  `stage_dirichlet_harmonic_exists`.
- Output: `u n : X → ℝ`, harmonic on `Ωcut n` away from marked singularities,
  continuous to the controlled boundary, with prescribed boundary values and
  normalization.
- Mathlib leaves: `HarmonicOnNhd`, `HarmonicContOnCl`, Poisson formulas on
  discs as local barriers/checks.
- Classification: hard own-subtree.  This is the worst single step.

B3. Maximum principle and uniform boundary control.

- Prove stage harmonic functions are uniformly bounded on compact patch
  subdomains away from singularities.
- Mathlib leaves:
  `Complex.norm_le_of_forall_mem_frontier_norm_le` for holomorphic functions
  after exponentiation; harmonic maximum principles may need local development.
- Classification: multi-commit hard.

B4. Harmonic conjugate on cut stages.

- New theorem shape:
  `stage_harmonic_conjugate_exists_on_cut`.
- Existing local leaves:
  `IsHarmonicConjugateAtReal.*`,
  `dipole_conjugate_exists_at_off_PQ`,
  `chart_pullback_dipole_has_conjugate_at_off_PQ`.
- Missing: global compatibility and period-killing on `Ωcut n`.
- Classification: hard own-subtree.

B5. Holomorphic stage coordinate.

- Define `f n` from `u n` and its conjugate, e.g. by
  `f n = exp (u n + I * v n)` or an integrated primitive variant.
- Prove chartwise differentiability/holomorphicity on `Ωcut n`.
- Mathlib leaves:
  `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`,
  complex differentiability/exponential APIs.
- Classification: multi-commit hard.

### C. Stage Normalization And Noncollapse

Status: NEW-WORK, serial.

C1. Normalize by marked values/derivative.

- Fix Mobius/scalar freedom so the chosen identity-chart patch has center
  value `0` and derivative `1`, and the inversion patch is compatible with
  infinity.
- Classification: hard multi-commit.

C2. Nonzero derivative at the normalized center.

- Prove the stage coordinate has nonzero derivative before scaling and exact
  normalized derivative after scaling.
- Leaves: local harmonic conjugate/holomorphic construction and maximum
  principle/open mapping style facts.
- Classification: hard multi-commit.

C3. Total stage map.

- Define `F n : X → OnePoint ℂ` by the normalized holomorphic stage map on
  `Ωcut n` and a fixed filler outside.
- Classification: routine one commit.

### D. Uniform Chart-Ball Estimates

Status: NEW-WORK, farmable after B/C.

D1. Eventual holomorphic chart readings.

- For each realized patch `i`, prove that for all large `n`,
  `fun x => (realizedPatch i).patch.targetChart (F n x)` is represented in
  the source chart by a differentiable function on the relevant ball.
- Green leaf:
  `ChartBallPowerSeries.ofDiffContOnCl`.
- Classification: routine/multi-commit.

D2. Uniform Cauchy-circle bounds.

- Use B3/C1 to produce a bound `M i r` independent of `n` on the Cauchy
  circles of each selected chart ball.
- Green consumers:
  `ChartBallPowerSeries.norm_deriv_le_of_sphere_bound`,
  `ChartBallPowerSeries.norm_image_sub_le_of_cauchy_bound`,
  `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`.
- Classification: hard/multi-commit, farmable per target chart.

D3. Compact target range.

- Provide compact target sets for the bounded continuous closed-ball readings.
- Green leaves:
  `ChartBallPowerSeries.boundedContinuousOnClosedBall`,
  `ChartBallPowerSeries.isCompact_closure_boundedContinuousOnClosedBall_range`.
- Classification: routine one commit.

### E. Finite Common Subsequence

Status: mixed; farmable with a serial final join.

E1. Local extraction per patch.

- Green leaf:
  `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`.
- Classification: routine once D is complete.

E2. Finite diagonal extraction.

- Green leaf:
  `exists_diagonal_subseq_tendstoLocallyUniformlyOn_finite`.
- Classification: green/routine once D supplies the hypotheses.

E3. Closed-ball to source-local convergence.

- Needed theorem:
  `stage_closedBall_to_patch_tendstoLocallyUniformlyOn`.
- Existing leaf:
  `tendstoLocallyUniformlyOn_of_tendstoUniformlyOn_subballs`.
- Classification: routine multi-commit.

E4. Filler irrelevance and subsequence reindexing.

- Needed theorem:
  `TendstoLocallyUniformlyOn.congr_eventually_on_source`.
- Existing leaf:
  `tendstoUniformlyOn_subseq`; add local-uniform analogue if absent.
- Classification: routine one commit.

### F. Normalized Limits And Realized Patches

Status: mostly green after E.

F1. Normalization persists.

- Green leaves:
  `ChartBallPowerSeries.limit_apply_center_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.deriv_limit_center_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.deriv_limit_center_ne_zero_of_tendstoLocallyUniformlyOn_chartBall`,
  `ChartBallPowerSeries.normalizedChartBallLimit_of_tendstoLocallyUniformlyOn`.
- Classification: routine after C/E.

F2. Local chart homeomorphism from normalized limit.

- Green leaves:
  `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit`,
  `GenusZeroLocalMontelChartPatch.ofChartBallLimit`.
- Classification: green/routine.

F3. Source-chart package and realized patch.

- Green leaves:
  `exists_sourceChartPackage_of_chartBallData`,
  `exists_montelRealizedPatch_of_chartBallData`,
  `montelRealizedPatch_of_sourceChartLocalSection`.
- Classification: green/routine.

### G. Overlap Agreement And Provider Payload

Status: serial final assembly.

G1. Common-sequence overlap agreement.

- Green consumer:
  `genusZeroMontel_normalized_limits_agree_on_overlaps`.
- Inputs: common sequence from E and normalized limits from F.
- Classification: routine after E/F.

G2. Representation by candidate `u`.

- Candidate `u` should be assembled from the realized local coordinates and
  overlap agreement, not from `_e` as a holomorphic map.
- Classification: hard/routine mix depending on existing gluing support.

G3. Exact final edge.

No interface reshape is required if the engine proves:

```lean
theorem genusZero_stage_engine_payload
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    ∃ (u : X ≃ₜ OnePoint ℂ)
      (PatchIndex : Type*) (_ : Fintype PatchIndex) (_ : Nonempty PatchIndex)
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
          (localPatch inversionIndex).chartBall.toFun)) ∧
      (∃ F : ℕ → X → OnePoint ℂ, ∀ i,
        TendstoLocallyUniformlyOn
          (fun n x => (realizedPatch i).patch.targetChart (F n x))
          (realizedPatch i).patch.coord Filter.atTop
          (realizedPatch i).patch.source) ∧
      (∀ i x, x ∈ (realizedPatch i).patch.source →
        (realizedPatch i).patch.targetChart.symm
          ((realizedPatch i).patch.coord x) = u x) ∧
      (∀ i z, z ∈ (realizedPatch i).patch.targetChart.target →
        (realizedPatch i).patch.invCoord z =
          u.symm ((realizedPatch i).patch.targetChart.symm z))
```

Then:

```lean
theorem genusZeroMontel_finite_cover_coord_representation_with_realized_patches
    ... (_e : X ≃ₜ OnePoint ℂ) :
    ... := by
  exact genusZero_stage_engine_payload X _e
```

A smaller interface is possible but manager-owned: prove only the common
sequence payload against already-realized patches,

```lean
∃ F : ℕ → X → OnePoint ℂ, ∀ i,
  TendstoLocallyUniformlyOn
    (fun n x => (realizedPatch i).patch.targetChart (F n x))
    (realizedPatch i).patch.coord Filter.atTop
    (realizedPatch i).patch.source
```

and let the existing provider assemble the remaining clauses.  This is flagged
as an optional reshape, not required.

## Division Of Labor

Serial spine:

- A2/A3: bordered exhaustion and cut system.
- B2/B4/B5: Dirichlet existence, conjugate, and holomorphic stage coordinate.
- C1/C2: normalization and noncollapse.
- G2/G3: candidate map and final provider assembly.

Farmable after E2 tex skeleton:

- A1/A4: marked control data and eventual containment.
- B1: logarithmic singular model packaging.
- B3 and D2/D3: maximum-principle bounds and Cauchy-circle estimates, split by
  target chart.
- E1/E2/E3/E4: local extraction, finite diagonal extraction, source-local transfer, and
  filler/subsequence packaging.
- F2/F3: local chart and source-chart realization packaging.

Load-bearing mass:

- The worst single node is B2, `stage_dirichlet_harmonic_exists`.
- The second hard node is B4, `stage_harmonic_conjugate_exists_on_cut`, because
  local conjugates must be made globally compatible on each cut stage.
- C1/C2 must be designed early because exact normalization is what makes the
  existing nondegeneration lemmas usable later.

## Proposed E2 Skeleton Nodes

- `lem:stage-marked-topological-control-data`
- `lem:stage-bordered-exhaustion-domains`
- `lem:stage-cut-domain-conjugate-control`
- `lem:stage-dirichlet-harmonic-exists`
- `lem:stage-dipole-boundary-control`
- `lem:stage-harmonic-conjugate-exists-on-cut`
- `lem:stage-holomorphic-coordinate-from-harmonic-dipole`
- `lem:stage-map-normalized-noncollapse`
- `lem:stage-chart-reading-uniform-cauchy-bound`
- `lem:stage-chart-reading-chartBallPowerSeries`
- `lem:stage-common-diagonal-subsequence`
- `lem:stage-total-filler-locally-uniform-irrelevance`
- `lem:stage-engine-common-sequence-payload`
- `lem:stage-engine-provider-final-edge`

## Search Log

- Read `docs/montel-phase05-stage-construction.md`.
- Inspected
  `genusZeroMontel_finite_cover_coord_representation_with_realized_patches` in
  `Jacobian/HolomorphicForms/GenusZeroUniformization.lean`.
- Inspected `MontelDiagonalExtraction.lean`, `MontelSourceChartCover.lean`,
  `MontelLocalPatchRealization.lean`, and `MontelOverlapAgreement.lean`.
- Inspected `HarmonicDipole.lean` and `HarmonicConjugate.lean`.
- Searched Mathlib for `Harmonic`, `Subharmonic`, `Poisson`, `Dirichlet`,
  `Maximum`, `MeanValue`, `RiemannMapping`, `Koebe`, `Caratheodory`, and
  `Perron`.
- Read local Mathlib files:
  `Mathlib.Analysis.Complex.RiemannMapping`,
  `Mathlib.Analysis.Complex.Harmonic.Analytic`,
  `Mathlib.Analysis.Complex.Harmonic.Poisson`,
  `Mathlib.Analysis.Complex.AbsMax`.
