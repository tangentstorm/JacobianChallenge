# Jacobian Challenge

A Lean 4 / Mathlib formalization project targeting the Jacobian variety of a
compact Riemann surface.

The public specification lives in `Jacobian/Challenge.lean` and asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps along holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- the identity `pushforward f (pullback f P) = degree f • P`.

Approach: the analytic period-lattice construction
`Jacobian X = H0(X, Ω¹)* / H1(X, Z)`, built up through reusable layers
(complex tori, holomorphic forms, period integration, Abel-Jacobi, degree).

See `plan.md` for the full roadmap, phase breakdown, anti-hack audit, and
delegation strategy for Aristotle.

## Progress Report

Last tick: 2026-04-25 initial setup ET

Overall Jacobian infrastructure progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  Lake project, root modules, work-packet files
Mathlib inventory         ████████████████████  100%  pinned v4.28.0 audit recorded
Complex torus quotient    ██░░░░░░░░░░░░░░░░░░   10%  statements drafted; quotient/lattice packets next
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  absent in Mathlib; future charted-space work
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  manifold form type absent
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  largest missing infrastructure
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  waits on periods
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  local analytic theory partly present

Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs: 0/5
Completed this tick: none
Integrated this tick: none
Failed/split this tick: none

Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass  `lake build Jacobian.Challenge`
Statement bank            pass  `lake build Jacobian.WorkPackets.StatementBank`
Current target            not run  no active implementation target yet

Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Create the first narrow `Jacobian/ComplexTorus` target file.
2. Submit quotient-map and lattice-preservation tasks to Aristotle.
3. Keep the quotient manifold layer out of scope until quotient/lattice API is stable.
