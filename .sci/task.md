# Worker jc0 — Milestone 0b.4: add reverse-transport blueprint subtree

## Assignment

Add the next reverse-direction transport chain from Milestone 0b to the
genus-zero blueprint, recorded honestly as depending on the open #232
uniformization frontier: the chain moves the
`OnePoint ℂ` holomorphic-one-form vanishing result across a sphere
homeomorphism and packages it as `analyticGenus_eq_zero_of_homeomorphic_sphere`.
This is a blueprint-only commit-sized step.

## Scope

- Edit only `tex/sections/04-branched-covers-genus-zero.tex` unless a blueprint
  macro/reference check proves a tiny adjacent TeX fix is necessary.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not alter the open #232/#233/#234 nodes.
- Do not mark the transport/genus-zero nodes `\leanok`: manager review confirms
  they reach open #232 through the uniformization upgrade.

## Target Nodes

Add or refine `\lean{}`-tracked blueprint nodes for the reverse-direction
transport chain:

- `exists_biholomorphism_to_OnePointCx_of_homeoSphere`
- `holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx`
- `analyticGenus_eq_zero_of_homeomorphic_sphere`

Wire the existing topological-sphere holomorphic-one-form vanishing node and
reverse-direction genus-zero discussion through the transport nodes, while
leaving the open uniformization target #232 visible and unchanged.

## Checklist

- [x] Inspect existing nodes for sphere homeomorphism, pullback of one-forms,
      `OnePoint ℂ` subsingleton, and topological-sphere vanishing in
      `tex/sections/04-branched-covers-genus-zero.tex`.
- [x] Confirm the target Lean declarations exist in
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Recheck manager feedback and source dependencies; the transport/genus
      nodes reach open #232 and must remain uncoloured.
- [x] Add or refine the reverse-transport nodes with real `\lean{}` names,
      honest `\uses` edges, and no false `\leanok`.
- [x] Rewire the relevant existing reverse-direction node(s) to use
      `analyticGenus_eq_zero_of_homeomorphic_sphere` where appropriate.
- [x] Run `scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if the wrapper stalls after the
      web stage, run the post-processing scripts directly and record the
      generated-artifact verification.
- [x] Commit exactly the scoped blueprint/task-ledger edit with normalized
      author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- Manager review/source dependency check: the transport declarations route
  through open #232, so `lem:holomorphic-one-form-equiv-of-homeo-sphere`,
  `lem:analytic-genus-homeomorphic-sphere-eq-onepoint`, and
  `thm:analytic-genus-zero-of-homeomorphic-sphere` are deliberately not
  marked `\leanok`.
- `python3 scripts/blueprint_audit.py`: 104 statement-style blocks, 103 with
  `\lean{...}`, 83 clean, 19 open/orange obligations. The four additional
  orange nodes are the visible reverse-transport chain that reaches open #232.
- `bash scripts/build-blueprint.sh`: web stage completed; wrapper stalled in the
  known ground-truth node-state phase and was stopped.
- Direct post-processing completed:
  `inject-layman-toggle.py`, `inject-theme-toggle.py`,
  `inject-depgraph-extras.py`, and `build_collapsible_dep_graph.py`.
- Generated artifact checks: 65 HTML files, 64 layman-toggle markers, 64
  theme-toggle markers, 63 collapsible graph links; required generated pages
  and `extra_styles.css` reference present.
