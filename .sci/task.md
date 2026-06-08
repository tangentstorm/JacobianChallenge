# Worker jc0 — Adjusted Milestone 0a: blueprint audit only

## Assignment

Audit the existing genus-zero blueprint nodes in
`tex/sections/04-branched-covers-genus-zero.tex` without editing the blueprint.
The deliverable for this adjusted step is only a manager-reviewable audit note
in this task file, plus verified status from the current scripts.

## Scope

- Do not edit `tex/sections/04-branched-covers-genus-zero.tex`.
- Do not edit Lean files.
- Do not edit `Jacobian/Challenge.lean`.
- Do not add, remove, or rewire blueprint nodes in this step.
- Restore or revert any accidental tracked-file edits before submitting.

## Checklist

- [x] Confirm `git status --short` has no tracked blueprint or Lean edits before
      beginning the audit.
- [x] Inspect the existing genus-zero section and list the current nodes around
      #232/#233/#234.
- [x] Run `scripts/list-sorries.py --text` and record the current reachable
      sorry status for the three target declarations.
- [x] Run `bash scripts/build-blueprint.sh` and record whether the current
      blueprint builds after the accidental TeX edit has been restored.
- [x] Run `scripts/blueprint_audit.py` and record the current audit summary.
- [x] Add an audit note below identifying the floating orange nodes and the
      smallest next Milestone 0b edit set.
- [x] Confirm `git status --short` has no unintended tracked edits before
      setting status for manager review.

## Audit Note

Initial tracked worktree state: `git status --short` was empty after restoring
`tex/sections/04-branched-covers-genus-zero.tex`; no Lean or blueprint files
were edited during this audit.

Final tracked worktree state before staging the audit note: `git status --short
--branch` reported only `## jc0-genus-zero-blueprint-audit...origin/main`;
there were no Lean or blueprint edits. Per manager review, this ignored
`.sci/task.md` audit note is force-added as the sole reviewable commit content.

Current genus-zero nodes around #232/#233/#234:

- `lem:section-localRepr-continuity`
- `lem:holomorphic-one-form-linearEquiv-to-OnePointCx`
- `lem:holomorphic-one-form-equiv-of-homeo-sphere`
- `thm:homeo-sphere-holomorphic-one-form-vanishing`
- `lem:identity-chart-coeff-contdiff`
- `lem:inversion-chart-coeff-continuous-at-zero`
- `lem:cotangent-transition-formula`
- `lem:onepoint-cx-chart-overlap-derivative`
- `lem:onepoint-cx-chart-overlap-pullback`
- `lem:uniformization-genus-zero-homeomorphism`
- `thm:uniformization-genus-zero-biholomorphism`
- `lem:exists-biholomorph-analyticgenus-zero`
- `lem:complex-simple-pole-principal-part-biholomorph`
- `lem:holomorphic-one-form-pullback-via-biholo`
- `lem:section-localRepr-identity-chart-contdiff`
- `lem:section-localRepr-inversion-chart-continuous-at-zero`

`scripts/list-sorries.py --text` reports the expected three reachable
genus-zero target sorries:

- `exists_biholomorph_onePoint_of_genus_zero` in
  `Jacobian/HolomorphicForms/GenusZeroClassification.lean`
- `complexSimplePolePrincipalPart_of_biholomorph_onePoint` in
  `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`
- `exists_biholomorph_onePoint_of_analyticGenus_zero` in
  `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`

`scripts/blueprint_audit.py` exits 0 and is back to the expected pre-rejection
shape: 94 statement-style blocks, 93 with `\lean{...}`, 1 marked `\notready`,
77 clean, and 15 `B:decls-exist-but-no-env-leanok` nodes. The genus-zero
members of that orange list are exactly #232/#233/#234:

- `thm:uniformization-genus-zero-biholomorphism`
- `lem:exists-biholomorph-analyticgenus-zero`
- `lem:complex-simple-pole-principal-part-biholomorph`

`bash scripts/build-blueprint.sh` was rerun after restoring the TeX file. The
manager's verification confirms it completed successfully when allowed to write
the generated blueprint files; the earlier non-escalated run failed only because
the sandbox could not write `blueprint/lean_decls`, not because of unresolved
labels or deleted genus-zero nodes.

Smallest next Milestone 0b edit set:

1. Add tracked nodes for the Liouville / vanishing chain:
   `entire_tendsto_zero_eq_zero`,
   `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`,
   `holomorphicOneForm_onePointCx_toFun_eq_zero`,
   `holomorphicOneForm_onePointCx_subsingleton`, and
   `analyticGenus_onePointCx_eq_zero`.
2. Add tracked nodes for chart coefficient extraction:
   `ContMDiffSection_localRepr_identityChart_contDiff`,
   `holomorphicOneFormCoeffContDiff`, and
   `holomorphicOneForm_coeff_entire`.
3. Add tracked nodes for inversion / decay:
   `ContMDiffSection_localRepr_inversionChart_continuousAt_zero`,
   `holomorphicOneForm_chartOverlap_pullback`, and
   `holomorphicOneForm_coeff_tendsto_zero`, with Mathlib leaves for
   `hasDerivAt_inv`, `tendsto_inv₀_cobounded'`, and
   `Metric.cobounded_eq_cocompact`.
4. Add tracked nodes for reverse-direction transport through
   `exists_biholomorphism_to_OnePointCx_of_homeoSphere`,
   `holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx`, and
   `analyticGenus_eq_zero_of_homeomorphic_sphere`.
5. Add tracked nodes for the forward gluing / uniformization assembly:
   `GenusZeroDegreeOneBiholomorphicRoute.*`, `genusZeroGlobalGluing_*`, and
   `exists_contMDiff_homeomorph_to_onePointCx`.
