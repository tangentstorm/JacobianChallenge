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

Last tick: 2026-04-27 10:00 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient API       ████████████████████  100%  FullComplexLattice + quotient
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ███████████░░░░░░░░░   54%  type/module/analyticGenus + complete genus order/positivity API + full toFun matrix + `evalLinearMap` complete linearity in form & vec slots + ext + witness positivity
Path integration/periods         ██████████████░░░░░░   69%  full bridge ladder + refl/translation chart instances + named API around periodPairing/periodSubgroup with closure + extensional carrier facts
Analytic Jacobian (group)        ██████░░░░░░░░░░░░░░   28%  abstract quotient group + full mk + integer-action vec-slot + zero-class characterizations + Nontrivial witness chain
Abel-Jacobi API                  ███████░░░░░░░░░░░░░   37%  witness skeleton + composition + vec-slot algebra + base-change + telescoping + genus/Nontrivial chain + explicit `mk`/periodSubgroup bridges
Trace/degree/push-pull           ██████░░░░░░░░░░░░░░   31%  pullbackFormsFun: full linearity + LinearMap bundle + id + comp-id/comp-const + const-of-const + mixed const/id + id-of-id + light bridge to HolomorphicForms.evalLinearMap + bundled vec-slot full linearity along id + bundled form-slot zero/neg/sub along id

Note: under the global hypothesis `mfderiv c.symm = id` (true for
translation-transition charts, e.g. the torus), the corrected
period machinery reduces to the simpler provisional one across all
5 integration layers (chartedForm → in-chart → via-chart →
cover-with → Pick). Concrete instances established for the refl
chart and the explicit `translationChart v` construction.
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 1/5 — `09cd85dd` canary QUEUED ~15h.
                      Backend still asleep. Canary is
                      submitted-redundant; kept as wake detector.
Integrated this tick (local Claude-owned, 4 lemmas):
                      NEW TraceDegree.PullbackFormsLinearMapIdEvalDist:
                      bundled form-slot zero/neg/sub/double-neg
                      vec-applied along id, via `evalLinearMap` map_*.
Submitted this tick:  none.
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
Periods.ChartLiftBoundary pass lake build Jacobian.Periods.ChartLiftBoundary (no sorry)
Periods.PathIntegralViaChartLinear pass lake build Jacobian.Periods.PathIntegralViaChartLinear (no sorry; _neg+_smul)
TraceDegree.PullbackFunSimpApply pass lake build Jacobian.TraceDegree.PullbackFunSimpApply (no sorry)
Periods.ChartedFormPullbackApplyLinear pass lake build Jacobian.Periods.ChartedFormPullbackApplyLinear (no sorry)
Periods.ChartedFormPullbackLinearMapApplyLinear pass lake build Jacobian.Periods.ChartedFormPullbackLinearMapApplyLinear (no sorry)
TraceDegree.PullbackFunAddSubApply pass lake build Jacobian.TraceDegree.PullbackFunAddSubApply (no sorry)
TraceDegree.PullbackFormsLinearMapApplyLinear pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear (no sorry)
Periods.PathIntegralViaChartCorrectSmulSymm pass lake build Jacobian.Periods.PathIntegralViaChartCorrectSmulSymm (no sorry)
Periods.PathIntegralChartCorrectSmulSymm pass lake build Jacobian.Periods.PathIntegralChartCorrectSmulSymm (no sorry)
Periods.PathIntegralChartSmulSymm pass lake build Jacobian.Periods.PathIntegralChartSmulSymm (no sorry)
Periods.PathIntegralViaChartSmulSymm pass lake build Jacobian.Periods.PathIntegralViaChartSmulSymm (no sorry)
Periods.PathIntegralViaChartCorrectSymmAddSelf pass lake build Jacobian.Periods.PathIntegralViaChartCorrectSymmAddSelf (no sorry)
Periods.PathIntegralViaCoverSymmAddSelf pass lake build Jacobian.Periods.PathIntegralViaCoverSymmAddSelf (no sorry)
Periods.PathIntegralChartCorrectSymmAddSelf pass lake build Jacobian.Periods.PathIntegralChartCorrectSymmAddSelf (no sorry)
Periods.PathIntegralChartSymmAddSelf pass lake build Jacobian.Periods.PathIntegralChartSymmAddSelf (no sorry)
Periods.PathIntegralViaChartSymmAddSelf pass lake build Jacobian.Periods.PathIntegralViaChartSymmAddSelf (no sorry)
Periods.PathIntegralChartCorrectTrans pass lake build Jacobian.Periods.PathIntegralChartCorrectTrans (no sorry)
Periods.PathIntegralChartTrans pass lake build Jacobian.Periods.PathIntegralChartTrans (no sorry)
TraceDegree.PullbackFunComp pass lake build Jacobian.TraceDegree.PullbackFunComp (no sorry)
TraceDegree.PullbackFunCompApply pass lake build Jacobian.TraceDegree.PullbackFunCompApply (no sorry)
TraceDegree.PullbackFormsLinearMapComp pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapComp (no sorry)
TraceDegree.PullbackFunCompConst pass lake build Jacobian.TraceDegree.PullbackFunCompConst (no sorry)
TraceDegree.PullbackFunConstComp pass lake build Jacobian.TraceDegree.PullbackFunConstComp (no sorry)
TraceDegree.PullbackFormsLinearMapCompConst pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapCompConst (no sorry)
Periods.PathIntegralViaChartCorrectNegSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaChartCorrectNegSymmEqSelf (no sorry)
Periods.PathIntegralViaCoverNegSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaCoverNegSymmEqSelf (no sorry)
Periods.PathIntegralChartCorrectNegSymmEqSelf pass lake build Jacobian.Periods.PathIntegralChartCorrectNegSymmEqSelf (no sorry)
Periods.PathIntegralChartNegSymmEqSelf pass lake build Jacobian.Periods.PathIntegralChartNegSymmEqSelf (no sorry)
Periods.PathIntegralViaChartNegSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaChartNegSymmEqSelf (no sorry)
Periods.ChartLiftTrans pass lake build Jacobian.Periods.ChartLiftTrans (no sorry)
Periods.ChartLiftTransApply pass lake build Jacobian.Periods.ChartLiftTransApply (no sorry)
Periods.PathIntegralViaChartCorrectTrans pass lake build Jacobian.Periods.PathIntegralViaChartCorrectTrans (no sorry)
Periods.PathIntegralViaChartTrans (canary — sorry'd, awaiting Aristotle)
Periods.PathIntegralViaChartCorrectSmulSymmEqNegSmul pass lake build Jacobian.Periods.PathIntegralViaChartCorrectSmulSymmEqNegSmul (no sorry)
Periods.PathIntegralViaCoverSmulSymmEqNegSmul pass lake build Jacobian.Periods.PathIntegralViaCoverSmulSymmEqNegSmul (no sorry)
Periods.PathIntegralChartCorrectSmulSymmEqNegSmul pass lake build Jacobian.Periods.PathIntegralChartCorrectSmulSymmEqNegSmul (no sorry)
Periods.PathIntegralChartSmulSymmEqNegSmul pass lake build Jacobian.Periods.PathIntegralChartSmulSymmEqNegSmul (no sorry)
Periods.PathIntegralViaChartSmulSymmEqNegSmul pass lake build Jacobian.Periods.PathIntegralViaChartSmulSymmEqNegSmul (no sorry)
TraceDegree.PullbackFunIdApplyVec pass lake build Jacobian.TraceDegree.PullbackFunIdApplyVec (no sorry)
TraceDegree.PullbackFormsLinearMapIdApplyVec pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapIdApplyVec (no sorry)
TraceDegree.PullbackFormsLinearMapConstApplyVec pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapConstApplyVec (no sorry)
TraceDegree.PullbackFunConstApplyVec pass lake build Jacobian.TraceDegree.PullbackFunConstApplyVec (no sorry)
Periods.PathIntegralChartCorrectNegSmul pass lake build Jacobian.Periods.PathIntegralChartCorrectNegSmul (no sorry)
Periods.PathIntegralViaChartCorrectNegSmul pass lake build Jacobian.Periods.PathIntegralViaChartCorrectNegSmul (no sorry)
Periods.PathIntegralViaCoverNegSmul pass lake build Jacobian.Periods.PathIntegralViaCoverNegSmul (no sorry)
Periods.PathIntegralChartNegSmul pass lake build Jacobian.Periods.PathIntegralChartNegSmul (no sorry)
Periods.PathIntegralViaChartNegSmul pass lake build Jacobian.Periods.PathIntegralViaChartNegSmul (no sorry)
Periods.PathIntegralViaChartCorrectNegSmulSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaChartCorrectNegSmulSymmEqSelf (no sorry)
Periods.PathIntegralViaCoverNegSmulSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaCoverNegSmulSymmEqSelf (no sorry)
Periods.PathIntegralChartCorrectNegSmulSymmEqSelf pass lake build Jacobian.Periods.PathIntegralChartCorrectNegSmulSymmEqSelf (no sorry)
Periods.PathIntegralChartNegSmulSymmEqSelf pass lake build Jacobian.Periods.PathIntegralChartNegSmulSymmEqSelf (no sorry)
Periods.PathIntegralViaChartNegSmulSymmEqSelf pass lake build Jacobian.Periods.PathIntegralViaChartNegSmulSymmEqSelf (no sorry)
Periods.PathIntegralChartCorrectSmulSmul pass lake build Jacobian.Periods.PathIntegralChartCorrectSmulSmul (no sorry)
Periods.PathIntegralViaChartCorrectSmulSmul pass lake build Jacobian.Periods.PathIntegralViaChartCorrectSmulSmul (no sorry)
Periods.PathIntegralViaCoverSmulSmul pass lake build Jacobian.Periods.PathIntegralViaCoverSmulSmul (no sorry)
Periods.PathIntegralChartSmulSmul pass lake build Jacobian.Periods.PathIntegralChartSmulSmul (no sorry)
Periods.PathIntegralViaChartSmulSmul pass lake build Jacobian.Periods.PathIntegralViaChartSmulSmul (no sorry)
Periods.PathIntegralChartCorrectNegEqNegOneSmul pass lake build Jacobian.Periods.PathIntegralChartCorrectNegEqNegOneSmul (no sorry)
Periods.PathIntegralViaChartCorrectNegEqNegOneSmul pass lake build Jacobian.Periods.PathIntegralViaChartCorrectNegEqNegOneSmul (no sorry)
Periods.PathIntegralViaCoverNegEqNegOneSmul pass lake build Jacobian.Periods.PathIntegralViaCoverNegEqNegOneSmul (no sorry)
Periods.PathIntegralChartNegEqNegOneSmul pass lake build Jacobian.Periods.PathIntegralChartNegEqNegOneSmul (no sorry)
TraceDegree.PullbackFunCompConstApply pass lake build Jacobian.TraceDegree.PullbackFunCompConstApply (no sorry)
TraceDegree.PullbackFormsLinearMapCompConstApplyVec pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapCompConstApplyVec (no sorry)
TraceDegree.PullbackFormsLinearMapCompIdApply pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapCompIdApply (no sorry)
TraceDegree.PullbackFunConstCompConst pass lake build Jacobian.TraceDegree.PullbackFunConstCompConst (no sorry)
TraceDegree.PullbackFunConstCompConstBundled pass lake build Jacobian.TraceDegree.PullbackFunConstCompConstBundled (no sorry)
TraceDegree.PullbackFunMixedConstIdApply pass lake build Jacobian.TraceDegree.PullbackFunMixedConstIdApply (no sorry)
TraceDegree.PullbackFormsLinearMapMixedConstId pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapMixedConstId (no sorry)
TraceDegree.PullbackFunIdComposeId pass lake build Jacobian.TraceDegree.PullbackFunIdComposeId (no sorry)
HolomorphicForms.AnalyticGenus pass lake build Jacobian.HolomorphicForms.AnalyticGenus (no sorry)
HolomorphicForms.AnalyticGenusPos pass lake build Jacobian.HolomorphicForms.AnalyticGenusPos (no sorry)
HolomorphicForms.ToFunApply pass lake build Jacobian.HolomorphicForms.ToFunApply (no sorry)
HolomorphicForms.ToFunApplyVec pass lake build Jacobian.HolomorphicForms.ToFunApplyVec (no sorry)
HolomorphicForms.ToFunApplyVecExtra pass lake build Jacobian.HolomorphicForms.ToFunApplyVecExtra (no sorry)
HolomorphicForms.ToFunNeg pass lake build Jacobian.HolomorphicForms.ToFunNeg (no sorry)
HolomorphicForms.EvalLinearMapNeg pass lake build Jacobian.HolomorphicForms.EvalLinearMapNeg (no sorry)
HolomorphicForms.EvalLinearMap pass lake build Jacobian.HolomorphicForms.EvalLinearMap (no sorry)
HolomorphicForms.EvalLinearMapApi pass lake build Jacobian.HolomorphicForms.EvalLinearMapApi (no sorry)
TraceDegree.PullbackFunEvalLinearMap pass lake build Jacobian.TraceDegree.PullbackFunEvalLinearMap (no sorry)
TraceDegree.PullbackFunIdEval pass lake build Jacobian.TraceDegree.PullbackFunIdEval (no sorry)
TraceDegree.PullbackFunIdEvalDist pass lake build Jacobian.TraceDegree.PullbackFunIdEvalDist (no sorry)
TraceDegree.PullbackFunIdEvalSmul pass lake build Jacobian.TraceDegree.PullbackFunIdEvalSmul (no sorry)
TraceDegree.PullbackFunIdEvalVec pass lake build Jacobian.TraceDegree.PullbackFunIdEvalVec (no sorry)
TraceDegree.PullbackFunIdEvalVecExtra pass lake build Jacobian.TraceDegree.PullbackFunIdEvalVecExtra (no sorry)
TraceDegree.PullbackFormsLinearMapIdEval pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapIdEval (no sorry)
TraceDegree.PullbackFormsLinearMapIdEvalVec pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec (no sorry)
TraceDegree.PullbackFormsLinearMapIdEvalVecExtra pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVecExtra (no sorry)
TraceDegree.PullbackFormsLinearMapIdEvalDist pass lake build Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalDist (no sorry)
HolomorphicForms.EvalLinearMapZsmul pass lake build Jacobian.HolomorphicForms.EvalLinearMapZsmul (no sorry)
HolomorphicForms.Ext pass lake build Jacobian.HolomorphicForms.Ext (no sorry)
HolomorphicForms.ExtEvalLinearMap pass lake build Jacobian.HolomorphicForms.ExtEvalLinearMap (no sorry)
HolomorphicForms.AnalyticGenusWitness pass lake build Jacobian.HolomorphicForms.AnalyticGenusWitness (no sorry)
HolomorphicForms.EvalLinearMapVec pass lake build Jacobian.HolomorphicForms.EvalLinearMapVec (no sorry)
HolomorphicForms.EvalLinearMapVecExtra pass lake build Jacobian.HolomorphicForms.EvalLinearMapVecExtra (no sorry)
HolomorphicForms.AnalyticGenusOrder pass lake build Jacobian.HolomorphicForms.AnalyticGenusOrder (no sorry)
Periods.PeriodFunctionalApi pass lake build Jacobian.Periods.PeriodFunctionalApi (no sorry)
Periods.PeriodSubgroupApi pass lake build Jacobian.Periods.PeriodSubgroupApi (no sorry)
Periods.PeriodSubgroupClosure pass lake build Jacobian.Periods.PeriodSubgroupClosure (no sorry)
Periods.PeriodSubgroupExt pass lake build Jacobian.Periods.PeriodSubgroupExt (no sorry)
AnalyticJacobian.Mk pass lake build Jacobian.AnalyticJacobian.Mk (no sorry)
AnalyticJacobian.MkOps pass lake build Jacobian.AnalyticJacobian.MkOps (no sorry)
AnalyticJacobian.MkExt pass lake build Jacobian.AnalyticJacobian.MkExt (no sorry)
AnalyticJacobian.MkMembership pass lake build Jacobian.AnalyticJacobian.MkMembership (no sorry)
AnalyticJacobian.MkArith pass lake build Jacobian.AnalyticJacobian.MkArith (no sorry)
AnalyticJacobian.MkPeriodPairing pass lake build Jacobian.AnalyticJacobian.MkPeriodPairing (no sorry)
AnalyticJacobian.MkPeriodPairingSmul pass lake build Jacobian.AnalyticJacobian.MkPeriodPairingSmul (no sorry)
AnalyticJacobian.EvalJacobianClassPeriodPairing pass lake build Jacobian.AnalyticJacobian.EvalJacobianClassPeriodPairing (no sorry)
AnalyticJacobian.EvalJacobianClassMember pass lake build Jacobian.AnalyticJacobian.EvalJacobianClassMember (no sorry)
AnalyticJacobian.EvalJacobianClass pass lake build Jacobian.AnalyticJacobian.EvalJacobianClass (no sorry)
AnalyticJacobian.EvalJacobianClassOps pass lake build Jacobian.AnalyticJacobian.EvalJacobianClassOps (no sorry)
AnalyticJacobian.EvalJacobianClassSmul pass lake build Jacobian.AnalyticJacobian.EvalJacobianClassSmul (no sorry)
AnalyticJacobian.EvalJacobianClassZero pass lake build Jacobian.AnalyticJacobian.EvalJacobianClassZero (no sorry)
AnalyticJacobian.NontrivialWitness pass lake build Jacobian.AnalyticJacobian.NontrivialWitness (no sorry)
AbelJacobi.Defs pass lake build Jacobian.AbelJacobi.Defs (no sorry)
AbelJacobi.Composition pass lake build Jacobian.AbelJacobi.Composition (no sorry)
AbelJacobi.Smul pass lake build Jacobian.AbelJacobi.Smul (no sorry)
AbelJacobi.BaseChange pass lake build Jacobian.AbelJacobi.BaseChange (no sorry)
AbelJacobi.Identities pass lake build Jacobian.AbelJacobi.Identities (no sorry)
AbelJacobi.Coset pass lake build Jacobian.AbelJacobi.Coset (no sorry)
AbelJacobi.Telescoping pass lake build Jacobian.AbelJacobi.Telescoping (no sorry)
AbelJacobi.Sum pass lake build Jacobian.AbelJacobi.Sum (no sorry)
AbelJacobi.Nontrivial pass lake build Jacobian.AbelJacobi.Nontrivial (no sorry)
AbelJacobi.GenusWitness pass lake build Jacobian.AbelJacobi.GenusWitness (no sorry)
AbelJacobi.Specialize pass lake build Jacobian.AbelJacobi.Specialize (no sorry)
AbelJacobi.WitnessMk pass lake build Jacobian.AbelJacobi.WitnessMk (no sorry)
AbelJacobi.Symmetry pass lake build Jacobian.AbelJacobi.Symmetry (no sorry)
AbelJacobi (umbrella) pass lake build Jacobian.AbelJacobi
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
