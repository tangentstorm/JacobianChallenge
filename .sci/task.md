SUGGESTED TASK: Milestone 0 baseline audit for Chapter 06 blueprint mapping.

Objective: inventory the current Chapter-06 blueprint nodes and verification
state before adding any new proof-tree nodes. This commit should only update
the planning/audit artifacts needed to record the baseline; it must not edit
Lean proofs or introduce blueprint rewiring beyond documenting confirmed
current-state findings.

Scope:
- Read `tex/sections/06-periods-and-riemann-bilinear.tex` and identify the
  existing Chapter-06 nodes, especially the nodes corresponding to the 8 open
  sorries listed in `goal.md`.
- Check which nodes currently have `\uses`, `\lean{}`, and green/lean-ok
  markers, and note any floating or under-decomposed proof skeletons.
- Run the baseline blueprint verification commands:
  - `bash scripts/build-blueprint.sh`
  - `scripts/blueprint_audit.py`
- Record the baseline findings in `.sci/result.md`, including any unresolved
  labels, audit failures, or confirmation that the baseline is clean.

Checklist:
- [x] Inventory current Chapter-06 blueprint nodes and the 8 sorry-frontier nodes.
- [x] Record each frontier node's current `\uses` / `\lean{}` / marker status.
- [x] Run `bash scripts/build-blueprint.sh` and capture the result.
- [x] Run `scripts/blueprint_audit.py` and capture the result.
- [x] Update `.sci/result.md` with the baseline audit summary and next mapping
      recommendation.
- [x] Leave `.sci/status-line` as `READY: Chapter 06 baseline blueprint audit`
      after committing the baseline audit.
