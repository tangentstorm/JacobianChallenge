# Result — A4 stage dipole boundary-control interface

Added `Jacobian.HolomorphicForms.StageDipoleBoundary` with statement-level
interfaces for stage boundary potentials, base normalization, marked-end
logarithmic dipole behavior, finite boundary-chart control, and compact
subdomain bounds.  The only new frontier obligation is
`exists_stageDipoleBoundaryControl`.

`lem:stage-dirichlet-harmonic-exists` will consume
`StageDipoleBoundaryControl.boundaryPotential`, `base_normalized`,
`has_pos_log_profile`, `has_neg_log_profile`, and the finite
`boundaryChartControl` package as the prescribed boundary/singularity data for
the later Perron/Dirichlet existence theorem.

`lem:stage-chart-reading-uniform-cauchy-bound` will consume
`StageDipoleBoundaryControl.compactBound` together with
`boundaryChartControl` to state maximum-principle and Cauchy-circle estimates
on selected compact chart balls once the harmonic stage solutions and
normalization exist.

`lem:stage-map-normalized-noncollapse` will consume the shared
`base_normalized` field and the marked-end logarithmic profile fields to keep
the eventual holomorphic stage maps tied to the A1 normalization data and to
separate the two marked ends before Montel extraction.

Named A4 open obligation introduced in `StageDipoleBoundary.lean`:
`exists_stageDipoleBoundaryControl`.
