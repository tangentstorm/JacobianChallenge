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

Last tick: 2026-04-25 00:39 EDT

```text
Overall Jacobian infrastructure progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  Lake project, root modules, work-packet files
Mathlib inventory         ████████████████████  100%  pinned v4.28.0 audit recorded
Complex torus quotient    █████░░░░░░░░░░░░░░░   25%  algebraic mk/map/map_id/map_comp done; ComplexTorus/Basic.lean carved with mk continuity/open-map lemmas
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  absent in Mathlib; future charted-space work
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  manifold form type absent
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  largest missing infrastructure
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  waits on periods
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  local analytic theory partly present
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5  (queue listed 10 unrelated FourColor jobs — none ours)
Completed this tick: none owned by this project
Integrated this tick: local discharges of mk_surjective/map/map_mk/map_id/map_comp in StatementBank
                     plus new file Jacobian/ComplexTorus/Basic.lean (mk_continuous, mk_isOpenQuotientMap, mk_isOpenMap)
Failed/split this tick: none
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass     lake build Jacobian.Challenge
Statement bank            pass     lake build Jacobian.WorkPackets.StatementBank
Current target            pass*    lake build Jacobian.ComplexTorus.Basic   (*one sorry: map_continuous)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Submit a bounded Aristotle job for map_continuous in Jacobian/ComplexTorus/Basic.lean.
2. Add 2–3 more bounded packets to the same file so we can run several Aristotle jobs in parallel.
3. Keep the quotient manifold layer out of scope until the quotient-group/lattice topological API is settled.
```
