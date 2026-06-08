SUGGESTED TASK: Milestone A1 survey and blueprint-map the Hurewicz substrate for #228/#229/#230.

Objective: begin the Chapter-06 Cluster A blueprint map by surveying the
existing sorry-free substrate around the three Hurewicz / singular-homology
frontiers in `Jacobian/Periods/Hurewicz.lean` and exposing that substrate as
`\\lean{}`-tracked blueprint nodes. This step should make the green proof
skeleton beneath #228, #229, and #230 visible before the final A2 frontier
rewiring pass.

Scope:
- Read `Jacobian/Periods/Hurewicz.lean` around:
  - `polygon4g_quotient_path_finite_lift_subdivision` (#228),
  - `polygon4g_partial_side_arc_homologous_to_edge_chain` (#229),
  - `edgeChain_sum_singular_boundary_scalar_coefficient_zero` (#230).
- Identify sorry-free declarations supporting:
  - quotient-path finite subdivision / chart-lift structure,
  - partial-side-arc to edge-chain comparison,
  - edge-chain / singular-boundary coefficient bookkeeping.
- Add compact `\\lean{}`-tracked green nodes in the relevant blueprint location
  (`tex/sections/05-polygonal-model.tex`, and `tex/sections/06-periods-and-riemann-bilinear.tex`
  only if needed for Chapter-06 cross-linking).
- Wire those new substrate nodes with `\\uses` to existing green nodes or honest
  Mathlib/project leaves, without marking the three open frontier nodes
  `\\leanok`.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- Confirm every new `\\lean{}` declaration exists.
- For every new node marked `\\leanok`, verify the corresponding Lean
  declarations are genuinely sorry-free using `rg`, `#print axioms`, and/or
  `sorries.jsonl` evidence.
- Run `scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh` if the environment permits a clean
  return; otherwise record the build-wrapper caveat in `.sci/result.md`.
- Update `.sci/result.md` with the A1 substrate map and the next A2 frontier
  wiring recommendation.

Checklist:
- [x] Survey `Hurewicz.lean` around #228/#229/#230 and identify green substrate
      declarations.
- [x] Add `\\lean{}`-tracked green blueprint nodes for the quotient-path /
      side-arc / edge-chain substrate.
- [x] Leave #228/#229/#230 open, but record how the new substrate nodes support
      their eventual A2 wiring.
- [x] Verify all new Lean declarations and green-ness claims.
- [x] Run `scripts/blueprint_audit.py`.
- [x] Run or honestly caveat `bash scripts/build-blueprint.sh`.
- [x] Update `.sci/result.md` with A1 findings and A2 recommendation.
- [x] Commit the tex/result/task/plan/sorries updates and set
      `.sci/status-line` to `READY: Chapter 06 A1 Hurewicz substrate map`.
