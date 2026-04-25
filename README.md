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

Last tick: 2026-04-25 13:19 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    ████████████████████  100%  ZLattice bridge sorry-free
Quotient manifold layer   ███░░░░░░░░░░░░░░░░░   15%  exists_chart_ball proven
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5
Completed this tick: 21cc9828 (ChartBall)
Integrated this tick: 21cc9828 — Aristotle followed the recipe
                      exactly: 4-line proof using
                      exists_pos_le_norm_of_discreteTopology +
                      mk_injOn_ball_of_isolation + mk_image_isOpen.
                      `exists_chart_ball` is sorry-free.
Failed/split this tick: none.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge        pass    lake build Jacobian.Challenge
Statement bank   pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus     pass    lake build Jacobian.ComplexTorus (after refactor)
ZLatticeRecon    pass    lake build Jacobian.ComplexTorus.ZLatticeRecon (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Carve first chart packet for Aristotle: small-ball
   open embedding `mk ∘ Subtype.val : Metric.ball v r → V ⧸ Λ.subgroup`
   for `r < δ / 2`. Combines IsolationAtZero (radius) +
   MkInjOnSmallBall (injectivity) + `QuotientAddGroup.isOpenMap_coe`
   + `QuotientAddGroup.continuous_mk`.
2. After the open embedding: assemble the
   `OpenPartialHomeomorph` instance (ChartedSpace atlas
   building block).
3. Stretch goal: chart-transition smoothness (transitions
   are translations by lattice elements, all linear → ω-smooth).
```
