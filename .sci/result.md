# Result — B4 stage harmonic conjugate-on-cuts interface

Added `Jacobian.HolomorphicForms.StageHarmonicConjugate` with
statement-level interfaces for stage conjugates on cut domains, A3
cut-readiness compatibility, pointwise `IsHarmonicConjugateAtReal` relation
to the B2 harmonic potential, base phase normalization, selected-compact
cut-domain compatibility, and inherited B2 compact bounds.  The only new
frontier obligation is `exists_stageHarmonicConjugatesOnCuts`.

`lem:stage-holomorphic-coordinate-from-harmonic-dipole` will consume
`StageHarmonicConjugatesOnCuts.harmonicConjugate` together with
`conjugateOnCut` and the B2 `harmonicPotential` to package the complex-valued
coordinate candidate on each cut stage.

`lem:stage-map-normalized-noncollapse` will consume
`base_phase_normalized`, the B2 base normalization, and the marked-end
singularity fields to fix a stable phase convention and prevent collapse in
the later normalized stage-map sequence.

`lem:stage-chart-reading-chartBallPowerSeries` will consume
`eventually_compactReady`, `compactReadyBound`, and
`compactBound_eq_dirichlet'` so selected chart-ball compacta can be read inside
cut domains while retaining the B2 compact-bound estimates needed for
chart-ball packaging.

Named B4 open obligation introduced in `StageHarmonicConjugate.lean`:
`exists_stageHarmonicConjugatesOnCuts`.
