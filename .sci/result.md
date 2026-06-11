# Result — B2 stage Dirichlet harmonic-solution interface

Added `Jacobian.HolomorphicForms.StageDirichlet` with statement-level
interfaces for stage-local harmonicity, boundary agreement on finite
boundary-chart pieces, real harmonic stage potentials, inherited
normalization, marked-end logarithmic behavior, and compact-subdomain bounds.
The only new frontier obligation is
`exists_stageDirichletHarmonicSolution`.

`lem:stage-harmonic-conjugate-exists-on-cut` will consume
`StageDirichletHarmonicSolution.harmonicPotential` together with
`harmonicOn_stage` and the A3 cut-domain readiness fields to state the global
single-valued conjugate package on each cut stage.

`lem:stage-holomorphic-coordinate-from-harmonic-dipole` will consume the
`harmonicPotential`, `has_pos_log_profile`, `has_neg_log_profile`, and
eventual conjugate data to package the complex-valued coordinate candidate
before target-chart normalization.

`lem:stage-chart-reading-uniform-cauchy-bound` will consume
`StageDirichletHarmonicSolution.compactBound`, `boundaryCompactBound`, and
`agrees_boundary` as the analytic estimate surface connecting B2 solutions to
the later Cauchy-circle and Montel chart-reading bounds.

Named B2 open obligation introduced in `StageDirichlet.lean`:
`exists_stageDirichletHarmonicSolution`.
