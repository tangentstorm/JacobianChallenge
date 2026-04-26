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

Last tick: 2026-04-26 02:30 EDT

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
Path integration/periods         ██████████░░░░░░░░░░   50%  multi-chart cover + linearity (zero/neg/smul) landed
Analytic Jacobian (group)        ██░░░░░░░░░░░░░░░░░░   10%  abstract quotient group only (not yet torus)
Abel-Jacobi API                  █░░░░░░░░░░░░░░░░░░░    5%  Queue F recon only
Trace/degree/push-pull           ███░░░░░░░░░░░░░░░░░   15%  pullbackFormsFun: full linearity + LinearMap bundle + id

Note: `chartedForm` currently misses the chart-derivative factor of
the genuine 1-form pullback, so the period machinery is correct only
for translation-transition charts (e.g. the torus case). To be fixed.
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 5/5. Three running (1%), two queued.
Integrated this tick: none.
Submitted this tick:  none (full pipeline).
Local progress: added Periods/PathReflSubpath.lean — `refl_subpath`
                (Path.refl a).subpath t₀ t₁ = Path.refl a via
                Path.ext + rfl. Useful primitive for future _refl
                lemmas on multi-chart integrals.
Attempted: pathIntegralViaCoverWith_refl — backed out due to
           dependent-range rewrite blocker.
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
