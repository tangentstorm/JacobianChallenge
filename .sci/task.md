# Worker jc0 — Milestone 0b.5: add forward global-gluing blueprint subtree

## Assignment

Add the next Milestone 0b blueprint slice for the genus-zero forward
uniformization route: the already-implemented global-gluing assembly that turns
a normalized Montel patch selector into a candidate map
`X → OnePoint ℂ`, verifies its local chart expressions, packages the inverse
branches, and records `ContMDiff` for the map and inverse.

This is a blueprint-only commit-sized step. It should make the forward
gluing substrate visible without claiming that the selector existence or final
uniformization root #232 is solved.

## Scope

- Edit only `tex/sections/04-branched-covers-genus-zero.tex` and
  `.sci/task.md`, unless a blueprint macro/reference check proves a tiny
  adjacent TeX fix is necessary.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not alter the open #232/#233/#234 Lean declarations.
- Do not mark `exists_contMDiff_homeomorph_to_onePointCx` or
  `exists_biholomorph_onePoint_of_genus_zero` as `\leanok`; both still route
  through the open #232 frontier.
- Mark a new gluing node `\leanok` only after confirming its declaration is not
  listed by `scripts/list-sorries.py --text` and does not depend on the #232
  root.

## Target Nodes

Add or refine `\lean{}`-tracked blueprint nodes for the forward global-gluing
assembly around `GenusZeroNormalizedMontelPatchSelector`:

- `genusZeroGlobalGluing_coord_mem_target_on_patch`
- `genusZeroGlobalGluing_toMap`
- `genusZeroGlobalGluing_toMap_eq_uniformization`
- `genusZeroGlobalGluing_overlap_compatible`
- `genusZeroGlobalGluing_toMap_target_mem_on_patch`
- `genusZeroGlobalGluing_toMap_exists`
- `genusZeroGlobalGluing_chart_expression_on_patch`
- `genusZeroGlobalGluing_invMap_exists`
- `genusZeroGlobalGluing_local_left_inverse_on_patch`
- `genusZeroGlobalGluing_local_right_inverse_on_target_chart`
- `genusZeroGlobalGluing_contMDiff_toMap`
- `genusZeroGlobalGluing_contMDiff_invMap`

Wire `thm:uniformization-genus-zero-biholomorphism` through this new subtree
and an explicit still-open selector/uniformization frontier, rather than the
current broad prose jump from normal-family extraction directly to a
biholomorphism.

## Checklist

- [x] Inspect the existing `sec:uniformization-lite-iter3` blueprint nodes and
      choose labels/placement for a forward global-gluing subsection.
- [x] Confirm the target Lean declarations exist in
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Run `scripts/list-sorries.py --text` and verify the target
      `genusZeroGlobalGluing_*` declarations are not listed as reachable
      sorries.
- [x] Add the forward global-gluing nodes with real `\lean{}` names, honest
      `\uses` edges, and `\leanok` only for genuinely green declarations.
- [x] Rewire `thm:uniformization-genus-zero-biholomorphism` to depend on the
      new global-gluing subtree plus the explicit open #232/selector frontier;
      keep the theorem itself uncoloured.
- [x] Run `python3 scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if the wrapper stalls after the
      web stage, run the post-processing scripts directly and record the
      generated-artifact verification.
- [x] Commit exactly the scoped blueprint/task-ledger edit with normalized
      author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `scripts/list-sorries.py --text`: 20 reachable sorries total; none of the
  target `genusZeroGlobalGluing_*` declarations are listed.
- `python3 scripts/blueprint_audit.py`: 116 statement-style blocks, 115 with
  `\lean{...}`, 95 clean, 19 existing open/orange obligations.
- `bash scripts/build-blueprint.sh`: completed all stages, wrote
  `blueprint/web/node-states.json` for 115 labelled nodes, and verified
  injected extras.
- Generated artifact checks: 65 HTML files, 64 layman-toggle markers, 64
  theme-toggle markers, 63 collapsible graph links; `node-states.json`,
  `index.html`, `dep_graph_collapsible.html`, and the `extra_styles.css`
  reference are present.
