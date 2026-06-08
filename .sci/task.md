SUGGESTED TASK: Milestone P5 blueprint-map the #227 period-pairing frontier.

Objective: update the Chapter-06 Lean Blueprint so the current direct #227
frontier

```lean
h1_basis_periodPairing_realKernel_trivial
```

has an explicit path through the zero `periodPairing` placeholder to the
intended chain-integration, Stokes, Riemann-bilinear, and Hermitian-positivity
inputs. This is a blueprint mapping task, not another Lean narrowing or source
boundary split.

Manager feedback addressed:
- Do not keep reshaping the same frontier.
- Treat the zero `periodPairing` implementation as an upstream-placeholder
  situation.
- Map the frontier in `tex/` down to named Mathlib / Stokes / Hodge leaves before
  proposing more implementation.
- Restore the lingering `.sci/result.md` deletion before the next commit.

Scope:
- Edit `tex/sections/06-periods-and-riemann-bilinear.tex`.
- Edit `sorries.jsonl` only through `bash scripts/build-blueprint.sh`.
- Update `.sci/task.md`, `.sci/plan.md`, and `.sci/status-line` as required by
  the worker protocol.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit Lean source files unless the manager explicitly redirects.
- Do not mark any open node with `\leanok`.

Implementation target:
- Add or extend blueprint nodes documenting that `periodPairing` /
  `periodPairingComplex` are currently zero placeholders.
- Name the intended nonzero chain-integration/descent provider(s) that must
  eventually replace the placeholder.
- Wire `h1_basis_periodPairing_realKernel_trivial` through `\uses` to those
  provider nodes, plus the existing Stokes-on-Riemann-surface-with-boundary,
  Riemann-bilinear identity, and Hermitian-positivity inputs.
- Include named Mathlib references in the text for the chain-integration leaves
  already referenced in Chapter 06, such as `Mathlib.MeasureTheory.Integral.*`
  and the circle-integral/interval-integral leaves cited near the period
  construction.
- Keep the public #227 Lean API and existing sorry-free assemblies unchanged.

Verification:
- Run `bash scripts/build-blueprint.sh`.
- Run `python3 scripts/blueprint_audit.py`.
- Run `python3 scripts/list-sorries.py --text`.
- Confirm `sorries.jsonl` still has direct `c:"sorry"` rows for
  `h1_basis_periodPairing_realKernel_trivial` and its blueprint node, with no
  stale direct root for `h1_basis_periodMatrix_realKernel_trivial`.

Checklist:
- [x] Restore `.sci/result.md` if still deleted.
- [x] Update the Chapter-06 blueprint period-pairing/provider nodes.
- [x] Wire the `\uses` chain from the #227 provider to the named leaves.
- [x] Build the blueprint and refresh `sorries.jsonl`.
- [x] Run the blueprint audit and sorry scan.
- [x] Confirm no Lean source/API changes were made.
- [ ] Commit the scoped blueprint/SCI/ledger edit and set `.sci/status-line` to
      `READY: Chapter 06 P5 blueprint period-pairing frontier map`.
