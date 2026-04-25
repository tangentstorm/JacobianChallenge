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

Last tick: 2026-04-25 00:50 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    █████░░░░░░░░░░░░░░░   25%  Basic + 4 packets
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  pending
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 5/5
  c97ef7ec  map_continuous           Basic.lean
  6e60ff64  mk_zero/eq_iff/eq_zero   Mk.lean
  4d2fa17c  map_zero/map_mk_add      MapMk.lean
  21a882aa  map_surjective           Surjective.lean
  e2c130cc  nhds_zero_eq             NhdsZero.lean
Completed this tick: none
Integrated this tick: none (all 5 still queued)
Failed/split this tick: none
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge       pass    lake build Jacobian.Challenge
Statement bank  pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus.*  pass*   lake build Jacobian.ComplexTorus.{Basic,Mk,...}
                        (* expected sorry warnings; one per packet)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Retrieve the 5 in-flight jobs; integrate clean patches.
2. Refill the queue with the next bounded Queue B packets.
3. Hold off on the quotient manifold layer until the easy
   quotient-group/lattice API in Basic.lean is closed.
```
