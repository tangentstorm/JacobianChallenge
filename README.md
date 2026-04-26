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

Last tick: 2026-04-25 21:48 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient           ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ██████░░░░░░░░░░░░░░   30%  type + module + analyticGenus
Path integration/periods         █████░░░░░░░░░░░░░░░   25%  pairing stated, subgroup defined
Abel-Jacobi API                  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull           ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle queue still wedged (5 unrelated
                    jobs QUEUED 7h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: extended
                          `Jacobian/Periods/PathIntegralChart.lean`
                          with two basic API lemmas (no sorries):
                          - `@[simp] pathIntegralInChart_refl`:
                            integral over a constant path is 0.
                            One-line wrapper of Mathlib's
                            `curveIntegral_refl`.
                          - `pathIntegralInChart_symm`: reversing
                            the path negates the integral. One-line
                            wrapper of `curveIntegral_symm`.
                          Both are immediate from existing Mathlib
                          API and don't add new opaques. They give
                          the chart-local integral the basic API
                          shape (zero on trivial paths, sign-reversal
                          under symmetry) so downstream definitions
                          can reason about it without unfolding to
                          `curveIntegral` directly.
Complex torus layer: complete. Queue D: chart-local path integral
                     now has basic API lemmas; integral 1-cycle,
                     period pairing (opaque) and period subgroup
                     in place. Multi-chart path integration is the
                     next substantive piece.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge          pass    lake build Jacobian.Challenge
Statement bank     pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus       pass    lake build Jacobian.ComplexTorus (umbrella)
IsManifold         pass    lake build Jacobian.ComplexTorus.IsManifold (no sorry)
Witness            pass    lake build Jacobian.ComplexTorus.Witness (no sorry)
MkSmooth           pass    lake build Jacobian.ComplexTorus.MkSmooth (no sorry)
AddSmooth          pass    lake build Jacobian.ComplexTorus.AddSmooth (no sorry)
NegSmooth          pass    lake build Jacobian.ComplexTorus.NegSmooth (no sorry)
LieAddGroup        pass    lake build Jacobian.ComplexTorus.LieAddGroup (no sorry)
HolomorphicForms.Recon pass lake build Jacobian.HolomorphicForms.Recon (recon, no sorry)
HolomorphicForms.CotangentBundle pass lake build Jacobian.HolomorphicForms.CotangentBundle (no sorry)
HolomorphicForms.Defs pass lake build Jacobian.HolomorphicForms.Defs (no sorry)
HolomorphicForms.FiniteDimensional pass lake build Jacobian.HolomorphicForms.FiniteDimensional (no sorry)
Periods.Recon       pass    lake build Jacobian.Periods.Recon (recon, no sorry)
Periods.ChartedForm pass    lake build Jacobian.Periods.ChartedForm (no sorry)
Periods.PathIntegralChart pass lake build Jacobian.Periods.PathIntegralChart (no sorry)
Periods.PathLift   pass    lake build Jacobian.Periods.PathLift (no sorry)
Periods.IntegralOneCycle pass lake build Jacobian.Periods.IntegralOneCycle (no sorry)
Periods.PeriodFunctional pass lake build Jacobian.Periods.PeriodFunctional (opaque pairing)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Multi-chart path integration: extend `pathIntegralViaChart` to
   paths that may cross chart boundaries via finite cover. With this
   in place, the `opaque periodPairing` can graduate to a real
   definition.
2. State the closedness and full-lattice properties of
   `periodSubgroup` as deferred lemmas (the actual proofs need
   Riemann bilinear / Hodge input).
3. Independently, attempt the torus sanity check
   (`analyticGenus ℂ (V ⧸ Λ.subgroup) ≥ 1` via constructing a
   non-trivial section).
```
