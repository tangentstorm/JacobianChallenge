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

Last tick: 2026-04-26 06:13 EDT

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
Path integration/periods         ███████████░░░░░░░░░   55%  multi-chart cover full linearity API; refl in flight
Analytic Jacobian (group)        ██░░░░░░░░░░░░░░░░░░   10%  abstract quotient group only (not yet torus)
Abel-Jacobi API                  █░░░░░░░░░░░░░░░░░░░    5%  Queue F recon only
Trace/degree/push-pull           ███░░░░░░░░░░░░░░░░░   17%  pullbackFormsFun: full linearity (+sub) + LinearMap bundle + id + tangent-vec apply

Note: `chartedForm` currently misses the chart-derivative factor of
the genuine 1-form pullback, so the period machinery is correct only
for translation-transition charts (e.g. the torus case). To be fixed.
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 3/5 (backend stalled ~57 min, no movement
                      since 04:09 EDT).
Integrated this tick: none — backend frozen.
Local progress this tick (Claude-owned, while Aristotle blocked):
                      No new lemma — conditional `_add`/`_sub`
                      ladders both span 3 layers (natural stopping
                      point). Bookkeeping tick: refresh status,
                      commit, push.
Still running (queued, no progress):
                      `f8faacda` Periods/ChartLiftBoundary
                      `bf7d62c4` Periods/PathIntegralViaChartLinear
                      `82687eb7` TraceDegree/PullbackFunSimpApply
Failed/split this tick: none.
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
Periods.PathIntegralViaChartCorrect pass lake build Jacobian.Periods.PathIntegralViaChartCorrect (no sorry)
Periods.ChartedFormPullbackSimp pass lake build Jacobian.Periods.ChartedFormPullbackSimp (no sorry)
TraceDegree.PullbackFun pass    lake build Jacobian.TraceDegree.PullbackFun (no sorry)
TraceDegree (umbrella) pass     lake build Jacobian.TraceDegree
Periods.PathIntegralViaChartCorrectZero pass lake build Jacobian.Periods.PathIntegralViaChartCorrectZero (no sorry)
Periods.ChartedFormPullbackSmul pass lake build Jacobian.Periods.ChartedFormPullbackSmul (no sorry)
TraceDegree.PullbackFunSmul pass lake build Jacobian.TraceDegree.PullbackFunSmul (no sorry)
Periods.DivFinIcc  pass    lake build Jacobian.Periods.DivFinIcc (no sorry)
Periods.PathIntegralChartCorrectLinear pass lake build Jacobian.Periods.PathIntegralChartCorrectLinear (no sorry; _neg only)
Periods.PathIntegralViaCover pass lake build Jacobian.Periods.PathIntegralViaCover (no sorry)
Periods.PathIntegralViaCoverZero pass lake build Jacobian.Periods.PathIntegralViaCoverZero (no sorry)
TraceDegree.PullbackFunId pass  lake build Jacobian.TraceDegree.PullbackFunId (no sorry)
Periods.PathIntegralChartCorrectSmul pass lake build Jacobian.Periods.PathIntegralChartCorrectSmul (no sorry)
TraceDegree.PullbackFormsLinearMap pass lake build Jacobian.TraceDegree.PullbackFormsLinearMap (no sorry)
Periods.ChartedFormPullbackLinearMap pass lake build Jacobian.Periods.ChartedFormPullbackLinearMap (no sorry)
Periods.PathIntegralViaChartCorrectNeg pass lake build Jacobian.Periods.PathIntegralViaChartCorrectNeg (no sorry)
Periods.PathIntegralViaCoverPick pass lake build Jacobian.Periods.PathIntegralViaCoverPick (no sorry)
Periods.PathIntegralViaChartCorrectSmul pass lake build Jacobian.Periods.PathIntegralViaChartCorrectSmul (no sorry)
Periods.PathIntegralViaCoverNeg pass lake build Jacobian.Periods.PathIntegralViaCoverNeg (no sorry)
TraceDegree.PullbackFormsLinearMapId pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapId (no sorry)
TraceDegree.PullbackFormsLinearMapSimp pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapSimp (no sorry)
Periods.ChartedFormPullbackLinearMapSimp pass lake build Jacobian.Periods.ChartedFormPullbackLinearMapSimp (no sorry)
Periods.PathReflSubpath pass lake build Jacobian.Periods.PathReflSubpath (no sorry)
Periods.PathIntegralViaCoverSmul pass lake build Jacobian.Periods.PathIntegralViaCoverSmul (no sorry)
Periods.PathIntegralViaCoverPickSimp pass lake build Jacobian.Periods.PathIntegralViaCoverPickSimp (no sorry)
TraceDegree.PullbackFormsLinearMapSmul pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapSmul (no sorry)
Periods.ChartedFormPullbackLinearMapSmul pass lake build Jacobian.Periods.ChartedFormPullbackLinearMapSmul (no sorry)
Periods.CurveIntegralLinearity pass lake build Jacobian.Periods.CurveIntegralLinearity (stub)
Periods.PathIntegralViaCoverPickSmul pass lake build Jacobian.Periods.PathIntegralViaCoverPickSmul (no sorry)
Periods.ChartLiftReflSubpath pass lake build Jacobian.Periods.ChartLiftReflSubpath (no sorry)
Periods.ChartedFormPullbackApply pass lake build Jacobian.Periods.ChartedFormPullbackApply (no sorry)
Periods.PathIntegralViaCoverWithRefl pass lake build Jacobian.Periods.PathIntegralViaCoverWithRefl (no sorry)
Periods.ChartedFormSmul pass lake build Jacobian.Periods.ChartedFormSmul (no sorry)
TraceDegree.PullbackFunConst pass lake build Jacobian.TraceDegree.PullbackFunConst (no sorry)
Periods.PathIntegralViaCoverWithApply pass lake build Jacobian.Periods.PathIntegralViaCoverWithApply (no sorry)
Periods.PathIntegralViaCoverPickRefl pass lake build Jacobian.Periods.PathIntegralViaCoverPickRefl (no sorry)
TraceDegree.PullbackFunApply pass lake build Jacobian.TraceDegree.PullbackFunApply (no sorry)
TraceDegree.PullbackFormsLinearMapConst pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapConst (no sorry)
Periods.PathIntegralViaCoverPickApply pass lake build Jacobian.Periods.PathIntegralViaCoverPickApply (no sorry)
Periods.PathLiftSimpFromX pass lake build Jacobian.Periods.PathLiftSimpFromX (no sorry)
TraceDegree.PullbackFunIdApply pass lake build Jacobian.TraceDegree.PullbackFunIdApply (no sorry)
Periods.ChartedFormPullbackLinearMapApply pass lake build Jacobian.Periods.ChartedFormPullbackLinearMapApply (no sorry)
TraceDegree.PullbackFormsLinearMapApply pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapApply (no sorry)
Periods.PathIntegralChartCorrectApply pass lake build Jacobian.Periods.PathIntegralChartCorrectApply (no sorry)
Periods.PathIntegralViaChartCorrectApply pass lake build Jacobian.Periods.PathIntegralViaChartCorrectApply (no sorry)
Periods.ChartLiftApply pass    lake build Jacobian.Periods.ChartLiftApply (no sorry)
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
