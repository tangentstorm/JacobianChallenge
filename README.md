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

Last tick: 2026-04-25 10:03 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    ███████████████████░   95%  topology/lattice layer closed
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  pending
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 3/5
  cb03cf32  mapClm_surjective             MapClmSurjective.lean QUEUED
  01dfbc1f  mkHom_ker                     MkHomKer.lean         QUEUED
  65e8da6e  mapClm_zero (zero CLM)        MapZero.lean          QUEUED
Completed this tick: none
Integrated this tick: none — refilled with 3 new bounded packets
Failed/split this tick: none
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge       pass    lake build Jacobian.Challenge
Statement bank  pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus    pass*   lake build Jacobian.ComplexTorus
                        (* expected sorry warnings; one per packet)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Topological-quotient layer is essentially closed. Refactor
   `FullComplexLattice` to drop `quotient_t2`/`quotient_compact`
   fields in favor of derived instances.
2. Sketch the manifold layer: charted-space structure on V ⧸ Λ.
3. Bridge to `ZLattice.IsZLattice` if Mathlib's predicate is
   compatible.
```
