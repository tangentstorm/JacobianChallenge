# Result - B5 stage holomorphic coordinate interface

Added `Jacobian.HolomorphicForms.StageHolomorphicCoordinate` with
statement-level interfaces for complex stage coordinate candidates, the
pointwise `u + I * v` formula from B2/B4 data, chart-local holomorphicity on
cut domains, inherited base value normalization, and selected-compact
readiness for later chart readings.  The only new frontier obligation is
`exists_stageHolomorphicCoordinatesFromHarmonicDipole`.

`lem:stage-map-normalized-noncollapse` will consume
`StageHolomorphicCoordinates.coordinate`, `coordinate_formula`, and
`base_value` as the unnormalized complex stage-map candidate before fixing the
normalization and noncollapse invariant.

`lem:stage-chart-reading-uniform-cauchy-bound` will consume
`holomorphicOnCut` and `selectedReadyBound` to state Cauchy-circle bounds on
selected compact chart balls once the normalized coordinate readings are
chosen.

`lem:stage-chart-reading-chartBallPowerSeries` will consume
`eventually_selectedReady`, `selectedReadyBound`, and
`selectedCompact_cutReady` so eventually contained selected chart balls can be
packaged as local holomorphic chart readings.

Named B5 open obligation introduced in `StageHolomorphicCoordinate.lean`:
`exists_stageHolomorphicCoordinatesFromHarmonicDipole`.
