SUGGESTED TASK: Milestone P3 refresh #227 blueprint and sorry graph for the period-matrix kernel root.

Objective: update the Chapter-06 blueprint wiring and generated sorry ledger so
issue #227 points at the current precise Type-0 frontier:

```lean
h1_basis_periodMatrix_realKernel_trivial
```

The accepted P1 split proved `h1_basis_periodCoordinate_linearIndependent`
sorry-free from this narrower real-kernel provider, but the current blueprint
text and `sorries.jsonl` still name the older public/broader declarations. This
task should refresh the graph without claiming the open provider is solved.

Scope:
- Work primarily in `tex/sections/06-periods-and-riemann-bilinear.tex` and
  `sorries.jsonl`.
- Add or revise a Chapter-06 node so the open #227 frontier names
  `JacobianChallenge.Periods.h1_basis_periodMatrix_realKernel_trivial`.
- Keep the public `lem:riemann-classical-real-li-input` story honest: it is now
  a sorry-free assembly from `RiemannClassicalPeriodBasis` and the selected H₁
  basis provider stack, not the direct `sorry`.
- Do not mark the new period-matrix kernel provider with `\leanok`.
- Preserve the existing green substrate nodes for
  `periodPairing_satisfies_bilinear_identity`,
  `hodge_form_posDef_on_periods`, and the algebraic positivity skeletons.
- Do not edit `Jacobian/Challenge.lean`.
- Avoid jc2/jc3/jc4/jc5 active Lean files; this should be blueprint/ledger
  work plus verification only.

Verification:
- Run `python3 scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh` to refresh `sorries.jsonl` and node
  colors.
- Run `python3 scripts/list-sorries.py --text` and confirm
  `h1_basis_periodMatrix_realKernel_trivial` remains the reachable
  `PeriodFunctional.lean` sorry.
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Solution`.
- Confirm `sorries.jsonl` contains a direct `c:"sorry"` row for
  `h1_basis_periodMatrix_realKernel_trivial` and no stale direct `c:"sorry"`
  row for `h1_basis_periodCoordinate_linearIndependent`.
- Commit exactly the scoped blueprint/ledger/SCI edit with normalized
  author/committer metadata and `Co-authored-by: Codex <codex@openai.com>`.

Checklist:
- [x] Update Chapter-06 blueprint wording/wiring for the new #227 root.
- [x] Refresh `sorries.jsonl`.
- [x] Run `python3 scripts/blueprint_audit.py`.
- [x] Run `bash scripts/build-blueprint.sh`.
- [x] Run `python3 scripts/list-sorries.py --text`.
- [x] Run `lake build Jacobian.Periods.PeriodFunctional`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Confirm the stale old direct #227 root is gone from `sorries.jsonl`.
- [x] Commit the scoped edit and set `.sci/status-line` to
      `READY: Chapter 06 P3 #227 blueprint kernel-root refresh`.
