# Worker jc0 — Milestone 0b.3: add inversion/decay blueprint subtree

## Assignment

Add the next GREEN substrate cluster from Milestone 0b to the genus-zero
blueprint: the inversion-chart / decay chain that turns inversion-chart
continuity plus the chart-overlap formula into cocompact decay of the finite
coefficient. This is a blueprint-only commit-sized step that should make the
route into the Liouville finite-vanishing node explicit.

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

Add or refine `\lean{}`-tracked blueprint nodes for the inversion / decay chain:

- `ContMDiffSection_localRepr_inversionChart_continuousAt_zero`
- `holomorphicOneForm_chartOverlap_pullback`
- `holomorphicOneForm_coeff_tendsto_zero`

Ensure the existing finite-point vanishing node
`lem:onepoint-holomorphic-one-form-finite-vanishing` depends on the new
coefficient-decay node rather than jumping directly through inversion
continuity and the cotangent transition formula.

The proof text should also cite the Mathlib leaves used by the decay assembly:
`hasDerivAt_inv`, `tendsto_inv₀_cobounded'`, and
`Metric.cobounded_eq_cocompact`.

## Checklist

- [x] Inspect existing inversion-chart, overlap-derivative, overlap-pullback,
      cotangent-transition, and finite-vanishing nodes in
      `tex/sections/04-branched-covers-genus-zero.tex`.
- [x] Confirm the target Lean declarations exist in
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Run `scripts/list-sorries.py --text` and verify none of the target
      inversion / decay declarations are listed as reachable sorries.
- [x] Add or refine the inversion / decay nodes with real `\lean{}` names and
      honest `\uses` edges.
- [x] Rewire `lem:onepoint-holomorphic-one-form-finite-vanishing` to depend on
      the new coefficient-decay node.
- [x] Run `scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if the wrapper stalls after the
      web stage, run the post-processing scripts directly and record the
      generated-artifact verification.
- [x] Commit exactly the scoped blueprint/task-ledger edit with normalized
      author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `scripts/list-sorries.py --text`: target inversion / decay declarations are
  not listed as reachable sorries; only the three expected genus-zero target
  sorries remain in this area.
- `scripts/blueprint_audit.py`: exits 0; statement blocks increase from 101 to
  102, clean blocks increase from 84 to 85, and the 15 orange nodes remain the
  same open obligations.
- `bash scripts/build-blueprint.sh`: web stage completed through
  `tex/sections/04-branched-covers-genus-zero.tex` with no unresolved-label
  errors. The tool session again did not return from node-state generation, so
  post-processing was run directly against the generated web files: layman
  toggle on 64/65 pages, theme picker on 64/65 pages, collapsible nav link on
  63/65 pages, required artifacts present, and `index.html` links
  `styles/extra_styles.css`.
