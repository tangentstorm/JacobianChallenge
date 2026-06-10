# Phase 0.5: stage construction plan for the global sequence

## Executive Conclusion

The non-circular shape must be an exhaustion-shaped stage construction:

```lean
F : ℕ → X → OnePoint ℂ
```

is a total function only because Lean statements require a total function.
Mathematically, `F n` is required to be holomorphic only on a growing stage
domain `Ω n ⊆ X`; outside `Ω n`, `F n` may be an arbitrary filler value.  For
each selected chart ball or compact patch used in the finite Montel cover, the
patch lies in `Ω n` for all sufficiently large `n`, so every
`TendstoLocallyUniformlyOn` payload sees only the holomorphic tail.

This resolves the formal circularity of asking for globally holomorphic maps
`X → OnePoint ℂ`: such maps are precisely meromorphic sphere maps, which is
what the construction is trying to produce.  However, it does **not** provide
the analytic stage maps.  The existing green substrate starts after one already
has uniformly bounded holomorphic chart-ball families.  It supplies
equicontinuity, closed-ball compactness extraction, normalization preservation,
and local chart packaging; it does not construct a nonconstant holomorphic map
on the stage domains from `_e`.

The honest Phase 0.5 conclusion is therefore:

*The total-function/exhaustion formulation is compatible with the current Lean
provider statements, but the actual stage construction requires a real
uniformization engine, at Perron/Dirichlet/Koebe scale.  It is not available in
the current green substrate.*

That is a manager-level strategy decision: either build such an analytic engine
locally, introduce it as an explicit frontier provider, or change strategy.

## Target Payload

The common-sequence payload currently demanded by the realized-patch coordinate
provider is:

```lean
∃ F : ℕ → X → OnePoint ℂ, ∀ i,
  TendstoLocallyUniformlyOn
    (fun n x => (realizedPatch i).patch.targetChart (F n x))
    (realizedPatch i).patch.coord Filter.atTop
    (realizedPatch i).patch.source
```

Lean declaration:

- `genusZeroMontel_finite_cover_coord_representation_with_realized_patches`
  in `Jacobian/HolomorphicForms/GenusZeroUniformization.lean`
- Status: open provider.

Blueprint support:

- `lem:montel-selector-local-limit-tied-to-global-homeomorphism` and
  `lem:montel-selector-normalized-transition-agreement` are the older selector
  planning nodes for the same idea.
- `lem:montel-selector-coord-represents-uniformization` and
  `lem:montel-selector-overlap-compatible-normalized-values` are downstream
  consumers.
- Status: open planning nodes.

The Phase 0.5 question is how the sequence `F` can be built without already
having a meromorphic sphere map.

## Non-Circularity Resolution

Do **not** require every `F n : X → OnePoint ℂ` to be globally holomorphic.
That is circular: a globally holomorphic map from a compact Riemann surface to
`OnePoint ℂ` is exactly the meromorphic-map object that Path A is trying to
construct.

Instead use staged maps:

```text
Ω 0 ⊆ Ω 1 ⊆ Ω 2 ⊆ ...
⋃ n, Ω n = X minus finitely many temporary boundary/cut pieces
F n is holomorphic on Ω n
F n is arbitrary outside Ω n
```

For every selected patch source `U_i` and for every compact set
`K ⊆ U_i` used to witness locally uniform convergence, there must be an index
`N = N(i, K)` such that `K ⊆ Ω n` for all `n ≥ N`.  Then the tail of

```lean
fun n x => (realizedPatch i).patch.targetChart (F n x)
```

is a holomorphic chart-reading on `K`; the finite initial garbage terms do not
affect convergence along `Filter.atTop`.

Existing support:

- `TendstoLocallyUniformlyOn` is already the topology used by the provider.
  Its tail-insensitivity should follow from filter facts, but no project lemma
  currently packages the statement "eventual equality on a set preserves
  `TendstoLocallyUniformlyOn`."
- `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall` extracts
  a uniformly convergent subsequence once a chart-ball sequence is already
  defined and bounded on a fixed closed ball.
- Status: the exhaustion/filler formulation is compatible with existing
  statement shapes, but the tail-holomorphic transfer needs routine packaging.

NEW ANALYTIC WORK entry: `eventually_holomorphic_tail_to_chartBall_family`.
This is routine packaging once stage maps and stage-domain membership are
available.

## Adopted Stage Shape

The only viable non-circular stage shape I can name is a Perron/Koebe-style
exhaustion construction:

1. Use the topological input `_e : X ≃ₜ OnePoint ℂ` only to choose topological
   control data: two marked regions corresponding to `0` and `∞`, a finite
   atlas refinement, and an exhaustion by compact bordered surfaces or chart
   polygons.
2. On each stage domain `Ω n`, solve a normalized analytic boundary-value
   problem that produces a holomorphic coordinate-like map
   `f_n : Ω n → ℂ` or `F_n : Ω n → OnePoint ℂ`.
3. Normalize the stage map at two or three marked points/prime ends to remove
   Möbius freedom and prevent collapse to a constant.
4. Extend `F_n` to a total function `X → OnePoint ℂ` by a fixed filler value
   outside `Ω n`.
5. On every selected chart ball eventually contained in `Ω n`, read
   `F_n` in the relevant public target chart and package that reading as a
   `ChartBallPowerSeries`.

There are two classical variants:

- **Perron/Dirichlet variant.**  Solve Dirichlet problems on `Ω n`, construct
  harmonic conjugates on the cut stage domain, exponentiate or integrate to get
  holomorphic stage coordinates, and normalize.
- **Koebe iteration variant.**  Iteratively correct local chart maps on a
  bordered exhaustion so transition defects shrink and the normalized maps form
  a normal family.

Neither variant is present in the repository as a green Lean substrate.  The
existing `ChartBallPowerSeries` API can package a holomorphic chart-ball map
after it exists; it does not solve a boundary-value problem or perform Koebe
iteration.

Exact existing support:

- `ChartBallPowerSeries.ofDiffContOnCl`
- `ChartBallPowerSeries.hasFPowerSeriesOnBall_of_diffContOnCl`
- `ChartBallPowerSeries.tendstoLocallyUniformlyOn_partialSum`
- `ChartBallPowerSeries.tendstoUniformlyOn_partialSum_of_lt`
- Status: green/sorry-free, but local and post-construction.

Missing support:

- A theorem constructing `Ω n`.
- A theorem solving the normalized stage problem on `Ω n`.
- A theorem proving stage-domain chart-readings are uniformly bounded on the
  selected balls.
- A theorem proving the normalized stage maps are nondegenerate.

These are hard analytic content, not routine packaging.

## Convergence Driver

Once stage chart-readings exist on the selected balls, convergence is driven by
normal-family compactness plus normalization:

1. Uniform boundedness on a slightly larger closed chart ball gives Cauchy
   derivative estimates.
2. Cauchy derivative estimates give equicontinuity on the smaller selected
   ball.
3. Equicontinuity plus compact target range gives compact closure in bounded
   continuous functions on the closed ball.
4. Arzela-Ascoli gives a subsequence converging uniformly on the closed ball.
5. A finite diagonal extraction gives one common subsequence for all selected
   chart balls.
6. The chosen normalization fixes center value and center derivative, so the
   limit is nonconstant and supplies a normalized chart-ball limit.

Existing green support for steps 1-4 and 6:

- `ChartBallPowerSeries.norm_deriv_le_of_sphere_bound`
- `ChartBallPowerSeries.norm_image_sub_le_of_cauchy_bound`
- `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`
- `ChartBallPowerSeries.boundedContinuousOnClosedBall`
- `ChartBallPowerSeries.isCompact_closure_boundedContinuousOnClosedBall_range`
- `ChartBallPowerSeries.exists_tendsto_subseq_boundedContinuousOnClosedBall`
- `ChartBallPowerSeries.tendstoUniformlyOn_of_tendsto_boundedContinuousOnClosedBall`
- `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`
- `ChartBallPowerSeries.normalizedChartBallLimit_of_tendstoLocallyUniformlyOn`
- Status: green/sorry-free local substrate.

Existing support for local chart promotion after convergence:

- `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData`
- `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit`
- `GenusZeroLocalMontelChartPatch.ofChartBallLimit`
- `montelRealizedPatch_of_sourceChartLocalSection`
- `montelSourceChartPackage.toRealizedPatch`
- Status: green/sorry-free packaging after the limit and source-chart package
  are available.

Missing support:

- The globally common stage sequence before restriction.
- Uniform bounds for its chart-readings.
- The finite diagonal theorem in the exact form needed for all selected
  patches, unless supplied by recent Phase-0 item 3 work under a different
  declaration name.
- The closed-ball-to-locally-uniform transfer in the exact patch-source form.

## Equicontinuity on Selected Balls

The current green equicontinuity theorem is conditional:

```lean
ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound
```

It requires:

- a family `data : ι → ChartBallPowerSeries`;
- common center information;
- a Cauchy radius whose closed circles stay inside the chart ball;
- a uniform bound `M` on the relevant Cauchy circles.

Thus equicontinuity is available only after the stage construction supplies
bounded chart-ball packages.  It is not a theorem saying that maps built from
the topological homeomorphism `_e` are equicontinuous.

For the proposed exhaustion-stage maps, one must prove:

```text
For each selected chart ball B_i and smaller closed ball K_i,
there exist N and M such that for all n ≥ N, the chart-reading of F n
is holomorphic on a larger ball and has norm ≤ M on the Cauchy circles.
```

This is where the actual stage construction matters.  Perron/Koebe stages
would provide the bound through boundary normalization, maximum principle, and
the chosen target normalization.  None of those global estimates are currently
green.

Existing support:

- `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound`
- `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall`
- Status: green/sorry-free conditional consumers.

Missing support:

- `stage_chart_reading_uniform_cauchy_bound`
- `stage_chart_reading_chartBallPowerSeries`
- `stage_chart_reading_eventually_on_selected_ball`
- Status: hard analytic stage estimates.

## Citation Table

| Step | Blueprint | Lean declaration | Status |
| --- | --- | --- | --- |
| Common-sequence payload | `lem:montel-selector-local-limit-tied-to-global-homeomorphism`, `lem:montel-selector-normalized-transition-agreement` | `genusZeroMontel_finite_cover_coord_representation_with_realized_patches` | open provider |
| Local chart-ball packaging | formalization note in `sec:uniformization-lite-iter3` | `ChartBallPowerSeries.ofDiffContOnCl`, `ChartBallPowerSeries.hasFPowerSeriesOnBall_of_diffContOnCl` | green |
| Cauchy derivative/equicontinuity | local Montel substrate bullet in `sec:uniformization-lite-iter3` | `ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound` | green conditional |
| Closed-ball compactness extraction | local Montel substrate bullet in `sec:uniformization-lite-iter3` | `ChartBallPowerSeries.exists_subseq_tendstoUniformlyOn_closedBall` | green conditional |
| Normalization preserved by convergence | local normalized chart-ball bullet | `ChartBallPowerSeries.normalizedChartBallLimit_of_tendstoLocallyUniformlyOn` | green conditional |
| Local chart homeomorphism from normalized limit | inverse-function local chart bullet | `ChartBallPowerSeries.exists_localNormalizedChartHomeomorphData_of_normalizedLimit` | green |
| Source-chart realization | `lem:montel-local-patch-realization` | `montelRealizedPatch_of_sourceChartLocalSection`, `montelSourceChartPackage.toRealizedPatch` | green |
| Overlap agreement from common sequence | `lem:montel-selector-overlap-compatible-normalized-values` | `genusZeroMontel_normalized_limits_agree_on_overlaps` | green modulo its hypotheses |
| Exhaustion-stage construction | no exact node | no declaration | hard new analytic work |
| Uniform bounds for stages | no exact node | no declaration | hard new analytic work |
| Tail/filler irrelevance for locally uniform convergence | no exact node | no declaration | routine packaging |

## NEW ANALYTIC WORK

### Hard analytic work

1. **Exhaustion by admissible stage domains.**
   Construct an increasing sequence of bordered/chart-polygon domains `Ω n`
   adapted to `_e` and to the selected finite chart cover.  Each selected
   chart ball must be eventually contained in every later `Ω n`.

2. **Normalized stage-map construction.**
   For each `Ω n`, construct a nonconstant holomorphic stage map to
   `OnePoint ℂ` or to a chart target, normalized at fixed marked data.  The
   likely classical source is Perron/Dirichlet or Koebe iteration, not any
   currently green project lemma.

3. **Uniform stage estimates.**
   Prove uniform Cauchy-circle bounds for the stage chart-readings on every
   selected chart ball.  This is what allows the existing conditional
   equicontinuity theorem to apply.

4. **Nondegeneration under normalization.**
   Prove the normalized stage sequence cannot collapse to a constant and that
   center value and derivative normalizations persist in the limit.

5. **Finite common subsequence in exact provider form.**
   Produce one subsequence of the total stage sequence that works for all
   selected patches simultaneously.  This is standard diagonal compactness once
   all local compactness inputs are available, but it must be stated against
   the actual `F : ℕ → X → OnePoint ℂ` payload.

### Routine packaging

6. **Total filler irrelevance.**
   If two sequences agree eventually on a set `U`, then replacing one by the
   other preserves `TendstoLocallyUniformlyOn` on `U`.  This packages the fact
   that arbitrary values outside `Ω n` do not affect patch-local convergence.

7. **Closed-ball convergence to patch-local convergence.**
   Convert uniform convergence on source-coordinate closed balls into
   `TendstoLocallyUniformlyOn` on the corresponding patch sources.

8. **Stage chart-readings as `ChartBallPowerSeries`.**
   Package each eventually holomorphic chart-reading on a selected ball using
   `ChartBallPowerSeries.ofDiffContOnCl` once differentiability on the open ball
   and continuity on the closed ball have been proved.

## Explicit Non-Substrate

The following declarations in
`Jacobian/HolomorphicForms/CompactRiemannSurface.lean` are not used as support:

- `chart_local_equicontinuous`
- `chart_local_arzela_ascoli`
- `global_totally_bounded_via_chart_cover`
- `lebesgue_number_chart_cover`
- `chart_diagonal_extraction`
- `global_sup_via_chart_max`

They currently prove only `True`.  Any real use of their mathematical content
belongs in the hard analytic work list above.

## Strategy Decision

Phase 0.5 does not uncover a small missing lemma.  It identifies the real
construction gap: the project needs an analytic engine that constructs
normalized holomorphic maps on an exhaustion from topological genus-zero data.
The existing green Montel substrate can compactify and package such a sequence
after it is built, but it does not build the sequence.

If Path A continues constructively, the next manager-level choice should be one
of:

1. Add a major frontier provider for Perron/Koebe stage maps and then let the
   existing Montel substrate consume it.
2. Build that Perron/Koebe engine lemma by lemma, accepting that this is a
   multi-week analytic development.
3. Change strategy and route the genus-zero biholomorphism through another
   already-available non-circular construction.
