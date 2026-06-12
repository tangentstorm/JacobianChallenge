# Module rot inventory — #232 substrate health sweep (jc10, 2026-06-11)

Report-only sweep (nothing fixed). HEAD at sweep time:
`60bf51214e5ba7cc108c4753665856bc4c3e1868` on
`thm/genus-zero-uniformization`.

## Summary

All **553** modules (`Jacobian.lean` + every `Jacobian/**/*.lean`) were
built individually with sequential `lake build <Mod>` (one held build
slot, 20-min watchdog, full logs kept locally). Result: **352 green**,
**110 green-with-sorries** (only known provider-sorry warnings),
**56 warning-anomaly** (3 root causes: one unused-variable linter hit,
the deprecated `SmoothSection` import, the deprecated `Path.subpathAux`
— table below), **35 FAIL**.
The 35 failures collapse to **5 rot sites**; the other 30 modules fail
only because their import cone contains a site. All 5 sites sit in the
**registered** cone (transitively imported by the root aggregators) —
so `lake build Jacobian` itself fails today, while `Jacobian.Solution`
builds (sorry-warnings only). Of the **38 dormant** modules (reachable
from no aggregator — the feared silent-rot population) **every one
builds**; the known-broken `WitnessSubArith` positive control was
repaired on-branch hours before the sweep (commit `dcc7da65`), which is
why it now passes — method FAIL-detection was validated separately.
All five sites smell like v4.28→v4.31-rc1 pin-migration fallout: three
are ℤ-smul (`*IntSmul`/`*Zsmul`) files failing with identical
"application type mismatch", the other two are tactic drift
(`rewrite` pattern lost; `unsolved goals`).

## Rot sites (5)

| # | Site (own build fails) | Registered? | First error (verbatim) | Blocked consumers |
|---|---|---|---|---|
| 1 | `Jacobian/HolomorphicForms/EvalLinearMapZsmul.lean` | registered | `error: Jacobian/HolomorphicForms/EvalLinearMapZsmul.lean:23:47: Application type mismatch: The argument` | 9 |
| 2 | `Jacobian/Periods/PathIntegralViaCoverSymm.lean` | registered | `error: Jacobian/Periods/PathIntegralViaCoverSymm.lean:34:60: unsolved goals` | 6 |
| 3 | `Jacobian/Periods/PathLiftSimp.lean` | registered | `error: Jacobian/Periods/PathLiftSimp.lean:21:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern` | 8 |
| 4 | `Jacobian/Periods/PeriodFunctionalIntSmul.lean` | registered | `error: Jacobian/Periods/PeriodFunctionalIntSmul.lean:26:32: Application type mismatch: The argument` | 3 |
| 5 | `Jacobian/TraceDegree/PullbackFormsLinearMapIntSmul.lean` | registered | `error: Jacobian/TraceDegree/PullbackFormsLinearMapIntSmul.lean:27:63: Application type mismatch: The argument` | 4 |

## Blocked-by detail (30 downstream failures)

**Blocked by `Jacobian/HolomorphicForms/EvalLinearMapZsmul.lean`** (9):

- `Jacobian.HolomorphicForms`
- `Jacobian.HolomorphicForms.ToFunZsmul`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalSmul`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEvalDist`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEvalSmul`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIdIdEvalVec`
- `Jacobian.TraceDegree.PullbackFunIdEvalSmul`
- `Jacobian.TraceDegree.PullbackFunIdEvalVec`
- `Jacobian.TraceDegree.PullbackFunIdEvalVecExtra`

**Blocked by `Jacobian/Periods/PathIntegralViaCoverSymm.lean`** (6):

- `Jacobian.Periods.PathIntegralViaCoverNegSmulSymmEqSelf`
- `Jacobian.Periods.PathIntegralViaCoverNegSymm`
- `Jacobian.Periods.PathIntegralViaCoverNegSymmEqSelf`
- `Jacobian.Periods.PathIntegralViaCoverSmulSymm`
- `Jacobian.Periods.PathIntegralViaCoverSmulSymmEqNegSmul`
- `Jacobian.Periods.PathIntegralViaCoverSymmAddSelf`

**Blocked by `Jacobian/Periods/PathLiftSimp.lean`** (8):

- `Jacobian`
- `Jacobian.Periods`
- `Jacobian.Periods.PathIntegralViaChartNegSmulSymmEqSelf`
- `Jacobian.Periods.PathIntegralViaChartNegSymm`
- `Jacobian.Periods.PathIntegralViaChartNegSymmEqSelf`
- `Jacobian.Periods.PathIntegralViaChartSmulSymm`
- `Jacobian.Periods.PathIntegralViaChartSmulSymmEqNegSmul`
- `Jacobian.Periods.PathIntegralViaChartSymmAddSelf`

**Blocked by `Jacobian/Periods/PeriodFunctionalIntSmul.lean`** (3):

- `Jacobian.AnalyticJacobian`
- `Jacobian.AnalyticJacobian.MkPeriodPairingCycleSmul`
- `Jacobian.Periods.PeriodSubgroupNeg`

**Blocked by `Jacobian/TraceDegree/PullbackFormsLinearMapIntSmul.lean`** (4):

- `Jacobian.TraceDegree`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIntSmulAdd`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIntSmulAddApplyVec`
- `Jacobian.TraceDegree.PullbackFormsLinearMapIntSmulApply`

## Warning anomalies (56 modules; 3 root causes, 5 verbatim signatures)

| Warning (verbatim, truncated) | Modules |
|---|---|
| `Jacobian/HolomorphicForms/HarmonicConjugate.lean:18:6: Variable name `v` is not explicitly referenced.` | 12 |
| `Jacobian/Periods/ChartedFormSimp.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.SmoothSection' has been deprecated: please replace this i` | 34 |
| `Jacobian/Periods/ChartedFormSmul.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.SmoothSection' has been deprecated: please replace this i` | 1 |
| `Jacobian/Periods/PathIntegralChartCorrectZero.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.SmoothSection' has been deprecated: please r` | 6 |
| `Jacobian/Periods/PathSymmSubpath.lean:38:13: `Path.subpathAux` has been deprecated: Use `Set.Icc.convexComb` instead` | 3 |

**`Jacobian/HolomorphicForms/HarmonicConjugate.lean:18:6: Variable name `v` is not explicitly reference`**: `Jacobian.HolomorphicForms.HarmonicConjugate`, `Jacobian.HolomorphicForms.PerronConjugateUniqueness`, `Jacobian.HolomorphicForms.PerronStageConjugateBridge`, `Jacobian.HolomorphicForms.PerronStageDipolePotential`, `Jacobian.HolomorphicForms.PerronStageDipoleProfile`, `Jacobian.HolomorphicForms.PerronStageHarmonicCompose`, `Jacobian.HolomorphicForms.PerronStageLogConjugate`, `Jacobian.HolomorphicForms.StageDipoleBoundary`, `Jacobian.HolomorphicForms.StageDirichlet`, `Jacobian.HolomorphicForms.StageHarmonicConjugate`, `Jacobian.HolomorphicForms.StageHolomorphicCoordinate`, `Jacobian.HolomorphicForms.StageNormalization`

**`Jacobian/Periods/ChartedFormSimp.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.SmoothSection' ha`**: `Jacobian.Periods.ChartedFormApplyApplyLinear`, `Jacobian.Periods.ChartedFormApplyLinear`, `Jacobian.Periods.ChartedFormCurveIntegrable`, `Jacobian.Periods.ChartedFormLinearMap`, `Jacobian.Periods.ChartedFormLinearMapApply`, `Jacobian.Periods.ChartedFormLinearMapApplyApplyLinear`, `Jacobian.Periods.ChartedFormLinearMapApplyLinear`, `Jacobian.Periods.ChartedFormLinearMapSimp`, `Jacobian.Periods.ChartedFormLinearMapSmul`, `Jacobian.Periods.ChartedFormPullbackLinearMapEqOfMfderivId`, `Jacobian.Periods.ChartedFormSimp`, `Jacobian.Periods.ChartedFormSub`, `Jacobian.Periods.PathIntegralChartAdd`, `Jacobian.Periods.PathIntegralChartLinear`, `Jacobian.Periods.PathIntegralChartNegEqNegOneSmul`, `Jacobian.Periods.PathIntegralChartNegSmul`, `Jacobian.Periods.PathIntegralChartNegSmulSymmEqSelf`, `Jacobian.Periods.PathIntegralChartNegSymm`, `Jacobian.Periods.PathIntegralChartNegSymmEqSelf`, `Jacobian.Periods.PathIntegralChartOneSmul`, `Jacobian.Periods.PathIntegralChartSmulSmul`, `Jacobian.Periods.PathIntegralChartSmulSymm`, `Jacobian.Periods.PathIntegralChartSmulSymmEqNegSmul`, `Jacobian.Periods.PathIntegralChartSub`, `Jacobian.Periods.PathIntegralReflChart`, `Jacobian.Periods.PathIntegralReflCover`, `Jacobian.Periods.PathIntegralViaChartAdd`, `Jacobian.Periods.PathIntegralViaChartLinear`, `Jacobian.Periods.PathIntegralViaChartNegEqNegOneSmul`, `Jacobian.Periods.PathIntegralViaChartNegSmul`, `Jacobian.Periods.PathIntegralViaChartOneSmul`, `Jacobian.Periods.PathIntegralViaChartSmulSmul`, `Jacobian.Periods.PathIntegralViaChartSub`, `Jacobian.Periods.TranslationChart`

**`Jacobian/Periods/ChartedFormSmul.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.SmoothSection' ha`**: `Jacobian.Periods.ChartedFormSmul`

**`Jacobian/Periods/PathIntegralChartCorrectZero.lean:1:0: 'Mathlib.Geometry.Manifold.VectorBundle.Smoo`**: `Jacobian.Periods.PathIntegralChartCorrectZero`, `Jacobian.Periods.PathIntegralViaChartCorrectZero`, `Jacobian.Periods.PathIntegralViaCoverPickNegEqNegOneSmul`, `Jacobian.Periods.PathIntegralViaCoverPickNegSmul`, `Jacobian.Periods.PathIntegralViaCoverPickSimp`, `Jacobian.Periods.PathIntegralViaCoverZero`

**`Jacobian/Periods/PathSymmSubpath.lean:38:13: `Path.subpathAux` has been deprecated: Use `Set.Icc.con`**: `Jacobian.Periods.PathIntegralSegmentSymm`, `Jacobian.Periods.PathPartitionSymm`, `Jacobian.Periods.PathSymmSubpath`

## TIMEOUT retry pass

Lexicographic order sweeps subtree aggregators before their members, so
two early modules hit the 20-minute watchdog on a cold cache:
`Jacobian.AbelJacobi`, `Jacobian.AbelJacobi.AnalyticOfCurveBasis`. Both
**pass** on the post-sweep warm-cache retry (sorry-warnings only). No
persistent timeouts.

## Positive control deviation

goal.md expected `Jacobian.AbelJacobi.WitnessSubArith` to FAIL; it
builds clean because commit `dcc7da65` (2026-06-11 11:36, "remove
duplicate witnessAbelJacobi_add_swap_eq_zero and fix resulting MkOps
build failures") repaired it on this branch before the sweep started.
Method FAIL-detection validated instead by (a) a fresh-cone build of the
control (3922 jobs, real compilation, rc=0), (b) a deliberate failing
build (`lake build Jacobian.NoSuchModuleXYZ` → rc=1, verbatim `error:`
captured), and (c) an earlier aborted sweep correctly recording FAIL
rows for every module.

## Dormant modules (38, all build)

- `Jacobian.Challenge`
- `Jacobian.HolomorphicForms.CMfldBumpStub`
- `Jacobian.HolomorphicForms.HarmonicConjugate`
- `Jacobian.HolomorphicForms.HarmonicDipole`
- `Jacobian.HolomorphicForms.MontelDiagonalExtraction`
- `Jacobian.HolomorphicForms.MontelForwardSmoothness`
- `Jacobian.HolomorphicForms.MontelGluedMapLocalAgreement`
- `Jacobian.HolomorphicForms.MontelInverseSmoothness`
- `Jacobian.HolomorphicForms.MontelLimitUnique`
- `Jacobian.HolomorphicForms.MontelLocalPatchRealization`
- `Jacobian.HolomorphicForms.MontelOverlapAgreement`
- `Jacobian.HolomorphicForms.MontelSourceChartCover`
- `Jacobian.HolomorphicForms.PerronConjugateUniqueness`
- `Jacobian.HolomorphicForms.PerronEngineE`
- `Jacobian.HolomorphicForms.PerronHarmonicMaxPrinciple`
- `Jacobian.HolomorphicForms.PerronHarnackLimit`
- `Jacobian.HolomorphicForms.PerronRemovableSingularity`
- `Jacobian.HolomorphicForms.PerronStageConjugateBridge`
- `Jacobian.HolomorphicForms.PerronStageDipolePotential`
- `Jacobian.HolomorphicForms.PerronStageDipoleProfile`
- `Jacobian.HolomorphicForms.PerronStageHarmonicCompose`
- `Jacobian.HolomorphicForms.PerronStageLogConjugate`
- `Jacobian.HolomorphicForms.PerronStageMarkedData`
- `Jacobian.HolomorphicForms.PerronStageMaxPrinciple`
- `Jacobian.HolomorphicForms.PerronSubOn`
- `Jacobian.HolomorphicForms.RRKMinusPointVanishing`
- `Jacobian.HolomorphicForms.RRNonconstantPoleDivisor`
- `Jacobian.HolomorphicForms.StageCutGeometry`
- `Jacobian.HolomorphicForms.StageDipoleBoundary`
- `Jacobian.HolomorphicForms.StageDirichlet`
- `Jacobian.HolomorphicForms.StageEventualContainment`
- `Jacobian.HolomorphicForms.StageExhaustion`
- `Jacobian.HolomorphicForms.StageFrontierChartCover`
- `Jacobian.HolomorphicForms.StageHarmonicConjugate`
- `Jacobian.HolomorphicForms.StageHolomorphicCoordinate`
- `Jacobian.HolomorphicForms.StageModelSequence`
- `Jacobian.HolomorphicForms.StageNormalization`
- `Jacobian.Periods.ChartOverlapDerivContinuous`

## Method

- Enumeration: `Jacobian.lean` + `find Jacobian -name '*.lean'` → 553
  dotted module names, lexicographic, the two root aggregators
  (`Jacobian.Solution`, `Jacobian`) swept last. (goal.md's "~115
  modules" was an undercount.)
- Sequential `lake build <Mod>`, no parallelism; one build slot held
  for the sweep via the same atomic-mkdir protocol as
  `.sci/bin/build-target.sh`; 20-min per-module watchdog; Mathlib
  oleans verified present pre-flight; abort sentinel for any
  `Building/Built Mathlib.*` line (never fired).
- Classification recomputed offline from the full per-module logs:
  FAIL = nonzero exit, first `error:` line verbatim, rot attributed to
  the file the error points at (own file ⇒ site, else blocked-by);
  WARN-ANOMALY = any warning other than ``declaration uses `sorry` ``;
  green-with-sorries = sorry-warnings only.
- Dormancy: transitive `import` closure of `Jacobian` +
  `Jacobian.Solution` over project modules ⇒ 515 registered / 38
  dormant.
