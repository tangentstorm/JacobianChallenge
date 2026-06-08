SUGGESTED TASK: Milestone V finalize the Chapter 06 blueprint-to-Mathlib plan.

Objective: complete Phase 1 by auditing the finished Chapter-06 blueprint map,
running the final verification commands, and writing the jc1/jc4/jc5 execution
split for the 8 remaining Chapter-06 sorries.

Scope:
- Audit the mapped Chapter-06 dependency graph across the three clusters:
  - Cluster B: #227 `riemann_classical_real_LI_input`, #241
    `riemann_classical_real_LI_inputU`, and #240
    `h1_basis_of_compact_riemann_surfaceU`.
  - Cluster A: #228 `polygon4g_quotient_path_finite_lift_subdivision`, #229
    `polygon4g_partial_side_arc_homologous_to_edge_chain`, and #230
    `edgeChain_sum_singular_boundary_scalar_coefficient_zero`.
  - Cluster C: #242
    `deRhamComparisonMap1_zero_period_primitiveExists_provider` and #243
    `hodgeRemainder_periodPayload_exact`.
- Confirm each green `\\lean{}` blueprint node is either graph-coloured
  `done` in `sorries.jsonl` or otherwise honestly justified as sorry-free.
- Confirm the 8 open frontier nodes remain unmarked by proof-level `\\leanok`
  and are graph-coloured as `sorry` or `sorry-dep` only where expected.
- Run the final blueprint checks:
  - `python3 scripts/blueprint_audit.py`
  - `bash scripts/build-blueprint.sh`
  - `lake build Jacobian.Solution`, if not already covered by the blueprint
    build refresh and feasible in the environment.
- Write `.sci/result.md` with the final execution split and ordering:
  - #227 must precede #241.
  - Cluster-A lift/side-arc work should precede #230 coefficient independence.
  - #242 and #243 should be split by de Rham primitive existence versus Hodge
    period-payload exactness.
  - Include cross-worker coordination notes for jc1 / jc4 / jc5.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- `python3 scripts/blueprint_audit.py` succeeds.
- `bash scripts/build-blueprint.sh` succeeds and any generated `sorries.jsonl`
  change is included.
- `lake build Jacobian.Solution` succeeds or any environment limitation is
  explicitly recorded in `.sci/result.md`.
- `.sci/result.md` contains a concrete jc1/jc4/jc5 split proposal.

Checklist:
- [x] Audit all Cluster A/B/C frontier and substrate graph rows in
      `sorries.jsonl`.
- [x] Confirm all green `\\lean{}` nodes are genuinely green and open frontier
      nodes are not marked with `\\leanok`.
- [x] Run `python3 scripts/blueprint_audit.py`.
- [x] Run `bash scripts/build-blueprint.sh`.
- [x] Run `lake build Jacobian.Solution` or record why the blueprint build's
      Lake refresh is the available verification.
- [x] Write the final jc1/jc4/jc5 execution split in `.sci/result.md`.
- [x] Stage any generated `sorries.jsonl` update.
- [x] Commit the result/task/plan/sorries updates and set `.sci/status-line` to
      `READY: Chapter 06 blueprint-to-Mathlib plan`.
