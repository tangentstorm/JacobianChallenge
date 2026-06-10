# Result — A2/A3 stage exhaustion interfaces

Added `Jacobian.HolomorphicForms.StageExhaustion` with statement-level
interfaces for selected compacta, bordered stage domains, finite boundary chart
control, cut domains, cut avoidance, and the named single-valued-conjugate
readiness predicate.

A4 will consume `StageBorderedExhaustion.stage`, `isOpen_stage`,
`eventually_contains_selected`, and `boundaryData` to formulate stage-local
Perron/Dirichlet harmonic data on each bordered domain without choosing new
topological exhaustions.

B2 will consume the shared `StageSelectedCompactFamily` eventual-containment
interfaces from `StageBorderedExhaustion` and `StageCutSystem` to keep the
Montel chart-ball compacta inside the active stage domains while comparing
stage readings on fixed compact sets.

B4 will consume `StageCutSystem.cutDomain`, `cutDomain_subset_stage`,
`cuts_avoid_selected_eventually`, and `conjugateReady` so harmonic conjugate
and single-valued holomorphic-coordinate tasks can depend on the cut-system
interface directly rather than reopening the A2/A3 topology construction.

Named A2/A3 open obligations introduced in `StageExhaustion.lean`:
`exists_stageBorderedExhaustion` and `exists_stageCutSystem`.
