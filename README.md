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

Last tick: 2026-04-25 21:30 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    ████████████████████  100%  ZLattice bridge sorry-free
Quotient manifold layer   ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle has been wedged server-wide; the
                    two in-flight jobs (LocalSectionRightInv,
                    LocalSectionContinuous) were proven locally and
                    the Aristotle copies cancelled.
Recent commits this session: localSection_mk, continuousOn_localSection,
                             chartAtBall, ChartedSpace instance, lint
                             cleanup (Basic.lean + Defs.lean),
                             TransitionSubMem, TransitionSubContinuous,
                             TransitionLocallyTranslate,
                             TransitionContDiffOn, IsManifold (sorry-free).
Quotient manifold layer: 100%. ChartedSpace + IsManifold both done,
                         no sorries. The HasGroupoid obligation
                         discharges via `mem_groupoid_of_pregroupoid`
                         + two `contDiffOn_localSection_mk` calls.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge        pass    lake build Jacobian.Challenge
Statement bank   pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus     pass    lake build Jacobian.ComplexTorus (with IsManifold)
IsManifold       pass    lake build Jacobian.ComplexTorus.IsManifold (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Lie-add-group structure on the quotient (smooth `+` and `-`).
   Both descend from the linear ambient operations through the
   chart machinery. Needed for `Jacobian X` to satisfy the public
   `LieAddGroup` requirement.
2. Begin Queue C: `HolomorphicOneForm`. First packet: define
   the type and prove the `AddCommGroup` / `Module ℂ` structure
   using existing differential-form API.
3. Stretch goal: state finite-dimensionality of holomorphic
   1-forms as a named theorem, even if the proof is deferred.
```
