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

Last tick: 2026-04-26 00:44 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient API       ████████████████████  100%  FullComplexLattice + quotient
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ██████░░░░░░░░░░░░░░   30%  type/module/analyticGenus
Path integration/periods         ████████░░░░░░░░░░░░   40%  multi-chart partition + correct pullback landed
Analytic Jacobian (group)        ██░░░░░░░░░░░░░░░░░░   10%  abstract quotient group only (not yet torus)
Abel-Jacobi API                  █░░░░░░░░░░░░░░░░░░░    5%  Queue F recon only
Trace/degree/push-pull           █░░░░░░░░░░░░░░░░░░░    5%  Queue G recon only

Note: `chartedForm` currently misses the chart-derivative factor of
the genuine 1-form pullback, so the period machinery is correct only
for translation-transition charts (e.g. the torus case). To be fixed.
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 4/5.
In flight:            `091ac5d1` — Periods/ChartedFormPullbackSimp
                      (chartedFormPullback_zero/_neg/_add).
                      `ee3ce016` — Periods/PathIntegralViaChartCorrect
                      (from-X wrapper def + _refl + _symm).
                      `fe592ee1` — Periods/PathIntegralChartCorrectLinear
                      (pathIntegralInChartCorrect_neg + _add, inline).
                      `0b8b1163` — TraceDegree/PullbackFun
                      (Queue G first packet: pullbackFormsFun + zero/neg/add).
Integrated this tick: none.
Failed/split this tick: none.
Local progress: added Periods/PathIntegralChartCorrectZero.lean
                (Claude-owned: pathIntegralInChartCorrect_zero
                via ContMDiffSection.coe_zero +
                ContinuousLinearMap.zero_comp). Periods umbrella
                rebuilds clean. Held to 4/5 because the
                obvious 5th candidates (multi-chart cover,
                pullbackFormsFun smoothness) gate on either
                Claude design work or the in-flight packets.
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
Periods.LebesgueChartRadius pass lake build Jacobian.Periods.LebesgueChartRadius (no sorry)
Periods.ChartBallAtPoint pass lake build Jacobian.Periods.ChartBallAtPoint (no sorry)
AnalyticJacobian.Defs pass lake build Jacobian.AnalyticJacobian.Defs (no sorry)
HolomorphicForms (umbrella) pass lake build Jacobian.HolomorphicForms
Periods (umbrella)  pass    lake build Jacobian.Periods (1 opaque)
AnalyticJacobian (umbrella) pass lake build Jacobian.AnalyticJacobian
AbelJacobi.Recon    pass    lake build Jacobian.AbelJacobi.Recon (recon)
TraceDegree.Recon   pass    lake build Jacobian.TraceDegree.Recon (recon)
Periods.ChartedFormPullback pass lake build Jacobian.Periods.ChartedFormPullback (no sorry)
Periods.ChartedFormSimp pass lake build Jacobian.Periods.ChartedFormSimp (no sorry)
Periods.PathPartition pass lake build Jacobian.Periods.PathPartition (no sorry)
Periods.PathIntegralChartCorrect pass lake build Jacobian.Periods.PathIntegralChartCorrect (no sorry)
Periods.PathLiftSimp pass lake build Jacobian.Periods.PathLiftSimp (no sorry)
Periods.PathIntegralChartCorrectSimp pass lake build Jacobian.Periods.PathIntegralChartCorrectSimp (no sorry)
Periods.PathIntegralChartCorrectZero pass lake build Jacobian.Periods.PathIntegralChartCorrectZero (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Integrate the four in-flight packets as they land
   (091ac5d1, ee3ce016, fe592ee1, 0b8b1163); wire each into
   the appropriate umbrella.
2. Submit `pullbackFormsFun_smooth` once 0b8b1163 lands —
   the substantive ContMDiff step for upgrading to
   HolomorphicOneForm E X via Queue G.
3. Submit pathIntegralViaChartCorrect linearity (zero/neg/add)
   once ee3ce016 + fe592ee1 land.
4. Begin Claude-owned design of multi-chart `pathIntegralViaCover`
   (subpath / affine reparam, then a clean Aristotle packet for
   the well-definedness lemmas).
5. Decomposed TorusExample retry (smaller helpers around the
   `Bundle.continuousLinearMap` constant-section roadblock that
   stalled `259b18a1`).
```
