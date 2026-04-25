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

Last tick: 2026-04-25 08:40 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    █████████████████░░░   85%  16 packets done incl. cocompact→compact
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  pending
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 4/5
  02468cd4  mk_image_isCompact/Open       MkImage.lean        IN_PROGRESS 2%
  98392eb4  mk_preimage_isOpen/Closed     MkPreimage.lean     IN_PROGRESS 1%
  0faaf3e5  mkHom (bundled →+)            MkBundled.lean      IN_PROGRESS 1%
  2649200e  range_mk = univ               MkRange.lean        QUEUED
Completed this tick: none
Integrated this tick: none — packets just spinning up
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
1. Integrate the 5 in-flight Queue B siblings as they return.
2. Once the topological-quotient layer is closed, plan the
   compactness-from-cocompact-lattice packet.
3. Hold off on the quotient manifold layer until then.
```
