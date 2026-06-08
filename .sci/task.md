SUGGESTED TASK: Milestone A2 wire the Hurewicz frontier leaves #228/#229/#230.

Objective: complete the Chapter-06 Cluster A blueprint map by refining the
three open Hurewicz nodes so each exposes only its genuine remaining frontier.
A1 added the green substrate nodes; this step should wire #228, #229, and #230
through those substrates and any additional honest frontier leaves already
visible in `Jacobian/Periods/Hurewicz.lean`, without claiming the open sorries
are green.

Scope:
- Re-read `tex/sections/05-polygonal-model.tex` around the A1 Hurewicz nodes
  and `Jacobian/Periods/Hurewicz.lean` around:
  - `polygon4g_quotient_path_finite_lift_subdivision` (#228),
  - `singular_one_simplex_subdivision_prism_homologous`,
  - `polygon4g_partial_side_arc_homologous_to_edge_chain` (#229),
  - `edgeChain_sum_singular_boundary_scalar_coefficient_zero` (#230).
- Refine the blueprint wiring so:
  - #228 separates quotient-chart finite-lift topology from the independent
    singular subdivision-prism frontier.
  - #229 is focused on the primitive side-strip geometry after endpoint-repair
    bookkeeping.
  - #230 is focused on homological edge-chain independence after the finite
    coefficient algebra.
- Add compact open frontier nodes only if needed to name genuine remaining
  blockers already present in Lean, especially the subdivision-prism leaf.
- Do not mark #228/#229/#230 or any other direct `sorry` declaration with
  proof-level `\\leanok`.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- Confirm every new `\\lean{}` declaration exists.
- Confirm every new green node is absent from `sorries.jsonl` or otherwise
  justified as sorry-free; direct `sorry` frontier nodes must remain ungreen.
- Run `python3 scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh` and include any generated
  `sorries.jsonl` update if the build changes it.
- Update `.sci/result.md` with the final A2 frontier map and the next C1
  recommendation.

Checklist:
- [x] Inspect the current A1 Hurewicz nodes and relevant Lean declarations.
- [x] Add or refine open frontier nodes for the genuine #228/#229/#230 leaves.
- [x] Wire #228/#229/#230 so each depends only on green substrate plus its
      genuine frontier leaf.
- [x] Verify new declarations and green/open status.
- [x] Run `python3 scripts/blueprint_audit.py`.
- [x] Run `bash scripts/build-blueprint.sh`.
- [x] Stage any generated `sorries.jsonl` update from the build.
- [x] Update `.sci/result.md` with A2 findings and C1 recommendation.
- [x] Commit the tex/result/task/sorries updates and set
      `.sci/status-line` to `READY: Chapter 06 A2 Hurewicz frontier wiring`.
