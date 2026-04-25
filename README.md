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

Last tick: 2026-04-25 11:45 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    ████████████████████  100%  ZLattice bridge sorry-free
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  pending discreteness packaging
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5
Completed this tick: 5c13793d (ZLatticeFundDom)
Integrated this tick: 5c13793d — packaging helper landed cleanly
                      and immediately wired into ZLatticeRecon to
                      drop the 5th-field sorry. The
                      ZLattice→FullComplexLattice bridge is now
                      sorry-free.
Failed/split this tick: none
Queue refill planned this tick (separate commit): isolation-at-zero
+ small-ball injectivity + discreteness reconnaissance (the user
flagged that closed cocompact ⇏ discrete in general, so the
manifold layer needs a careful packaging step before chart packets).
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge        pass    lake build Jacobian.Challenge
Statement bank   pass    lake build Jacobian.WorkPackets.StatementBank
ZLatticeFundDom  pass    lake build Jacobian.ComplexTorus.ZLatticeFundDom
ZLatticeRecon    pass    lake build Jacobian.ComplexTorus.ZLatticeRecon (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Decide the FullComplexLattice discreteness packaging
   (likely add a `DiscreteTopology subgroup` field; closed
   cocompact alone is insufficient — `ℝ × ℤ ⊂ ℝ²`).
2. Submit IsolationAtZero + MkInjOnSmallBall + DiscretenessRecon
   packets to feed manifold-layer chart construction.
3. After (1) lands, carve the first chart packet (small-ball
   open embedding) per ManifoldRecon outline.
```
