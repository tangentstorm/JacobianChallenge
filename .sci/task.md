# Worker jc0 — Milestone 0b.1: add Liouville/vanishing blueprint subtree

## Assignment

Add the first GREEN substrate cluster from Milestone 0b to the genus-zero
blueprint: the Liouville / vanishing chain proving that holomorphic one-forms on
`OnePoint ℂ` vanish. This is a blueprint-only commit-sized step that should make
the reverse-direction genus-zero subtree more honest without touching Lean
proofs or the open #232/#233/#234 declarations.

## Scope

- Edit only `tex/sections/04-branched-covers-genus-zero.tex` unless a blueprint
  macro/reference check proves a tiny adjacent TeX fix is necessary.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not mark a node `\leanok` unless the declaration is absent from
  `scripts/list-sorries.py --text` and is already represented by an existing
  Lean declaration.
- Do not rewire #232/#233/#234 yet except where an existing reverse-direction
  node needs to use the new Liouville subtree.

## Target Nodes

Add or refine `\lean{}`-tracked blueprint nodes for this chain:

- `entire_tendsto_zero_eq_zero`
- `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
- `holomorphicOneForm_onePointCx_toFun_eq_zero`
- `holomorphicOneForm_onePointCx_subsingleton`
- `analyticGenus_onePointCx_eq_zero`

The leaf for `entire_tendsto_zero_eq_zero` should cite the Mathlib lemma
`Differentiable.eq_zero_of_tendsto_zero_cocompact` in prose or a Mathlib
reference node, as appropriate for existing blueprint style.

## Checklist

- [x] Inspect the existing genus-zero blueprint section around the chart
      coefficient, cotangent transition, and reverse-direction analytic-genus
      nodes to choose stable insertion points and labels.
- [x] Confirm the target Lean declarations exist in
      `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- [x] Run `scripts/list-sorries.py --text` and verify none of the target
      Liouville / vanishing declarations are listed as reachable sorries.
- [x] Add the Liouville / vanishing nodes with real `\lean{}` names and
      `\uses` edges to existing chart/decay nodes where those dependencies are
      already represented.
- [x] Rewire the existing reverse-direction vanishing / analytic-genus node to
      use `analyticGenus_onePointCx_eq_zero` or
      `holomorphicOneForm_onePointCx_subsingleton` as appropriate.
- [x] Run `scripts/blueprint_audit.py` and fix any new audit issues.
- [x] Run `bash scripts/build-blueprint.sh`; if sandboxing blocks generated
      blueprint writes, rerun with the required approval and record the result.
- [x] Commit exactly the blueprint edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `scripts/list-sorries.py --text`: target Liouville / vanishing declarations
  are not listed as reachable sorries; only the three expected genus-zero target
  sorries remain in this area.
- `scripts/blueprint_audit.py`: exits 0; statement blocks increase from 94 to
  99, clean blocks increase from 77 to 82, and the 15 orange nodes remain the
  same open obligations.
- `bash scripts/build-blueprint.sh`: exits 0; writes 98 labelled node states and
  verifies the Plain-English toggle, theme picker, and collapsible nav link.
