# Plan — jc4: source-chart cover package (Phase-0 item 5)

Tracking #232. One-to-two commits at lemma granularity. All work in NEW own
file `MontelSourceChartCover.lean`.

## M-A — Survey + exact statement (fold into the M-B commit if quick)
- Read jc1's Phase-0 §4 ("Build realized patches…") and your own constructor
  `montelRealizedPatch_of_sourceChartLocalSection` hypothesis list:
  `source`, `isOpen_source`, `sourceChart`, `sourceSection`,
  `sourceChart_contMDiffOn`, `sourceChart_mem_ball`,
  `sourceChart_mem_domainBall`, `sourceSection_rightInverse_onLocal`,
  `sourceSection_leftInverse`.
- Decide the package's input data: a point `p : X`, a `ChartBallPowerSeries`
  with `LocalNormalizedChartHomeomorphData` (+ whatever centering/radius facts
  the construction genuinely supplies — hypotheses, not assumptions pulled
  from thin air).

## M-B — The package lemma (the deliverable)
One existential package theorem, e.g.
`exists_sourceChartPackage_of_chartBallData`: under the M-A hypotheses,
∃ source set (open, containing p), `sourceChart`, `sourceSection` satisfying
ALL the constructor hypotheses — so the construction gets a
`MontelRealizedPatch` per selected patch by ONE application of your
constructor. Likely route: `sourceChart` from X's chart at `p` composed with
the chart-ball normalization; `sourceSection` from the chart's `symm`;
memberships by shrinking to a small enough ball (continuity); section
inverses from the chart's `left_inv`/`right_inv` on the shrunken set.
Substrate: X's `ChartedSpace`/`StableChartAt` API, your round-trip machinery,
`LocalNormalizedChartHomeomorphData` fields. If ONE genuine analytic fact is
missing (e.g. a `contMDiffOn` for the chart composition), isolate it as the
single named open sub-lemma.

## M-C (optional rider, only if clean) — the realized-patch corollary
`exists_montelRealizedPatch_of_chartBallData`: compose M-B with your
constructor for the one-call form jc1's construction will actually invoke.

## Verification (every commit)
Narrow wrapper build; `#print axioms` (expect clean); blueprint node
`lem:montel-source-chart-package` `\uses` your realization/constructor nodes,
`\leanok` only proved+clean; DepGraph root for the new file; audit + graph;
trailer; push; ancestry.
