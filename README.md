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

Last tick: 2026-04-25 12:28 EDT

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
Completed this tick: 8d77f7d8 (IsolationAtZero)
Integrated this tick: 8d77f7d8 — clean proof using
                      `isOpen_inter_eq_singleton_of_mem_discrete` +
                      `SetLike.isDiscrete_iff_discreteTopology`. All
                      three primitives needed for chart layer
                      (isolation, injectivity, recon) are now in.
Failed/split this tick: none.
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
1. Wait for 8d77f7d8 (IsolationAtZero) to land; its proof
   chain is the natural source of the isolation constant for
   chart construction.
2. Claude-owned FullComplexLattice refactor: add
   `isDiscrete : DiscreteTopology subgroup` field per
   c5beb23a's recommended option (a). Wire in
   ZLatticeRecon's `discreteTopology_toAddSubgroup` bridge.
3. After (2): carve first chart packet (small-ball open
   embedding) — IsolationAtZero gives the radius,
   MkInjOnSmallBall gives the injectivity, isDiscrete +
   isOpenMap_coe give the open embedding.
```
