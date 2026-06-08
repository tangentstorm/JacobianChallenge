# Worker jc0 — Milestone 0b.2: add chart-coefficient extraction blueprint subtree

## Assignment

Add the next GREEN substrate cluster from Milestone 0b to the genus-zero
blueprint: the identity-chart coefficient extraction chain. This is a
blueprint-only commit-sized step that should make the route from a holomorphic
one-form section to an entire coefficient function explicit, below the
Liouville / finite-vanishing node added in Milestone 0b.1.

## Scope

- Edit only `tex/sections/04-branched-covers-genus-zero.tex` unless a blueprint
  macro/reference check proves a tiny adjacent TeX fix is necessary.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not alter the open #232/#233/#234 nodes.
- Do not mark a node `\leanok` unless the declaration is absent from
  `scripts/list-sorries.py --text` and is already represented by an existing
  Lean declaration.

## Target Nodes

Add or refine `\lean{}`-tracked blueprint nodes for the chart-coefficient
extraction chain:

- `ContMDiffSection_localRepr_identityChart_contDiff`
- `holomorphicOneFormCoeffContDiff`
- `holomorphicOneForm_coeff_entire`

Wire the existing finite-point vanishing node
`lem:onepoint-holomorphic-one-form-finite-vanishing` through the new
`holomorphicOneForm_coeff_entire` node, so its `\uses` edge no longer jumps
directly from identity-chart smoothness to Liouville.

## Checklist

- [x] Inspect the existing chart-coefficient nodes and labels in
      `tex/sections/04-branched-covers-genus-zero.tex`.
- [x] Confirm the target Lean declarations exist in
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Run `scripts/list-sorries.py --text` and verify none of the target
      chart-coefficient declarations are listed as reachable sorries.
- [x] Add or refine the chart-coefficient extraction nodes with real
      `\lean{}` names and honest `\uses` edges.
- [x] Rewire `lem:onepoint-holomorphic-one-form-finite-vanishing` to depend on
      the new entire-coefficient node.
- [x] Run `scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if sandboxing blocks generated
      blueprint writes, rerun with the required approval and record the result.
- [x] Commit exactly the scoped blueprint/task-ledger edit with normalized
      author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `scripts/list-sorries.py --text`: target chart-coefficient declarations are
  not listed as reachable sorries; only the three expected genus-zero target
  sorries remain in this area.
- `scripts/blueprint_audit.py`: exits 0; statement blocks increase from 99 to
  101, clean blocks increase from 82 to 84, and the 15 orange nodes remain the
  same open obligations.
- `bash scripts/build-blueprint.sh`: web stage completed through
  `tex/sections/04-branched-covers-genus-zero.tex` with no unresolved-label
  errors. The tool session did not return from the node-state phase, so the
  post-processing steps were run directly: layman toggle on 64/65 pages, theme
  picker on 63/65 pages, collapsible nav link on 63/65 pages, required
  artifacts present, and `index.html` links `styles/extra_styles.css`.
