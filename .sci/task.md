SUGGESTED TASK: Milestone B1 survey and blueprint-map the #227 Riemann-bilinear substrate.

Objective: begin the Chapter-06 blueprint-to-Mathlib mapping with the keystone
cluster. Survey the existing sorry-free project substrate beneath
`riemann_classical_real_LI_input` and add the first explicit `\lean{}`-tracked
blueprint nodes for that substrate in
`tex/sections/06-periods-and-riemann-bilinear.tex`, so #227 no longer hangs as
an undecomposed single analytical gap.

Scope:
- Read `Jacobian/Periods/PeriodFunctional.lean` and the referenced
  Riemann-bilinear helper files to identify the green declarations already
  supporting:
  - the algebraic symplectic-period fold / bilinear stand-in,
  - Hermitian-positivity stand-ins,
  - the named frontier obligations feeding `riemann_classical_real_LI_input`.
- In `tex/sections/06-periods-and-riemann-bilinear.tex`, add a compact set of
  new lemma nodes with real `\lean{}` declarations for those green helpers and
  wire them with `\uses` to existing green nodes or named Mathlib facts.
- Rewire `lem:riemann-classical-real-li-input` to use those new nodes plus the
  genuine remaining frontier leaves; do not mark #227 itself `\leanok`.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- Confirm every new `\lean{}` declaration exists.
- For every new node marked `\leanok`, verify the corresponding Lean declaration
  is genuinely sorry-free using the available sorry audit evidence.
- Run `scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh` if the environment permits a clean
  return; otherwise record the same build-wrapper caveat in `.sci/result.md`.
- Update `.sci/result.md` with the B1 mapping summary and the next recommended
  B2 step for #241/#240.

Checklist:
- [x] Survey `PeriodFunctional.lean` and adjacent Riemann-bilinear helper files
      for green #227 substrate declarations.
- [x] Add `\lean{}`-tracked B1 blueprint nodes for the sorry-free bilinear and
      positivity substrate.
- [x] Rewire `lem:riemann-classical-real-li-input` to those substrate nodes and
      the genuine remaining frontier leaves.
- [x] Verify new Lean declarations and green-ness claims.
- [x] Run `scripts/blueprint_audit.py`.
- [x] Run or honestly caveat `bash scripts/build-blueprint.sh`.
- [x] Update `.sci/result.md` with B1 findings and B2 recommendation.
- [x] Commit the tex/result/task/plan updates and set `.sci/status-line` to
      `READY: Chapter 06 B1 Riemann-bilinear substrate map`.
