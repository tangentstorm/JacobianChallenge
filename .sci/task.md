# Worker jc0 — Milestone 0c: wire the genus-zero orange frontier

## Assignment

Finish the Milestone 0 blueprint mapping by tightening the orange frontier
around the three remaining genus-zero obligations #232/#233/#234. The goal is
to make the blueprint show exactly which pieces are already green substrate and
which pieces remain genuine open providers, without changing Lean code.

This is a blueprint-only commit-sized step. It should wire
`exists_biholomorph_onePoint_of_genus_zero`,
`exists_biholomorph_onePoint_of_analyticGenus_zero`, and
`complexSimplePolePrincipalPart_of_biholomorph_onePoint` through the already
mapped substrate and through explicit open frontier nodes, so the next Lean
proof work has a precise target.

## Scope

- Edit only `tex/sections/04-branched-covers-genus-zero.tex` and
  `.sci/task.md`, unless a blueprint macro/reference check proves a tiny
  adjacent TeX fix is necessary.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not alter the open #232/#233/#234 Lean declarations.
- Do not mark #232/#233/#234 or any wrapper that reaches them as `\leanok`.
- Do not claim the Riemann--Roch single-pole chain proves #234; keep the
  circularity guard explicit.

## Target Work

Add or refine blueprint nodes and `\uses` edges so that:

- #232 is visibly the remaining selector/uniformization frontier above the
  green global-gluing subtree.
- #233 is visibly a thin analytic-genus-zero packaging layer depending on the
  topological sphere direction and #232.
- #234 is visibly the principal-part frontier from an explicit biholomorphism,
  with `singlePoleAnalyticData_of_biholomorph_onePoint` shown as green assembly
  on top only if its declaration is confirmed sorry-free.
- `genusZero_singlePoleMeromorphicAnalyticData_nonempty` is shown as downstream
  assembly through #233 and the explicit-biholomorphism single-pole bridge, not
  through the circular RR fixed-pole chain.

Potential `\lean{}` declarations to inspect and map:

- `exists_biholomorph_onePoint_of_genus_zero`
- `exists_biholomorph_onePoint_of_analyticGenus_zero`
- `complexSimplePolePrincipalPart_of_biholomorph_onePoint`
- `singlePoleAnalyticData_of_biholomorph_onePoint`
- `genusZero_singlePoleMeromorphicAnalyticData_nonempty`

## Checklist

- [x] Inspect the current #232/#233/#234 blueprint nodes and nearby
      meromorphic single-pole nodes in
      `tex/sections/04-branched-covers-genus-zero.tex`.
- [x] Confirm the candidate Lean declarations exist in
      `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` and
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Run `scripts/list-sorries.py --text` and classify the candidate
      declarations as green substrate or open wrappers.
- [x] Add/refine the orange frontier nodes and downstream green assembly nodes
      with honest `\uses` edges and `\lean{}` names.
- [x] Ensure no node reaching #232/#233/#234 is marked `\leanok`.
- [x] Keep the circularity note explicit: #234 must be derived from an explicit
      biholomorphism, not from the RR fixed-pole chain that depends on the
      genus-zero single-pole package.
- [x] Run `python3 scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if the wrapper stalls after the
      web stage, run the post-processing scripts directly and record the
      generated-artifact verification.
- [x] Commit exactly the scoped blueprint/task-ledger edit with normalized
      author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `scripts/list-sorries.py --text`: 20 reachable sorries total. The direct
  genus-zero open wrappers remain #232, #233, and #234; downstream wrappers
  that call them are left uncoloured.
- `python3 scripts/blueprint_audit.py`: 122 statement-style blocks, 121 with
  `\lean{...}`, 99 clean, 21 existing/open orange obligations.
- `bash scripts/build-blueprint.sh`: completed all stages, wrote
  `blueprint/web/node-states.json` for 121 labelled nodes, and verified
  injected extras.
- Generated artifact checks: 65 HTML files, 64 layman-toggle markers, 64
  theme-toggle markers, 63 collapsible graph links; `node-states.json`,
  `index.html`, `dep_graph_collapsible.html`, and the `extra_styles.css`
  reference are present.
