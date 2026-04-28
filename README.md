This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-28 09:47 EDT

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 116        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  383 / 392    counting `:= sorry`-ending lines per file. 8 files with
                                          real sorries — see below.

Reproduction: for f in <files>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
Open sorries by file (all production sorries; 8 files, 21 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface  2   Banach data, Montel
  HolomorphicForms/GenusZeroClassification 4  finite/infty Liouville leaves +
                                              uniformization-lite + hard-direction unif.
  Periods/PeriodFunctional                2   IsZLattice integrality + Riemann-bilinear nondegeneracy
  AbelJacobi/AnalyticOfCurveBasis         2   path-integral smoothness + Abel-injectivity
  ComplexTorus/ULiftTransport             2   ULift transition obligations
  TraceDegree/PullbackBasis               3   basisDualPullback companions (id, mk_eq, comp)
  TraceDegree/PushforwardBasis            5   complex-torus smoothness + pushforwardTraceLift_{id,preserves_lattice,mk_spec,comp_spec}
  TraceDegree/AnalyticDegree              1   anti-hack #4 trace-pullback identity (named _spec)
```

```text
StatementBank promotion (curated ratio)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                          promoted / total   notes
ComplexTorus                 3 / 3           Prop placeholders backed by IsManifold + LieAddGroup
HolomorphicForms             3 / 3           abbrev/def used directly as the working types
Periods                      1 / 6           IntegralOneCycle concrete; periodFunctional opaque;
                                             period_homology / period_pairing_full_rank still placeholders
AnalyticJacobian             1 / 3           AnalyticJacobianType ✓; equiv/homeomorph_challenge placeholders
AbelJacobi                   0 / 2           pathIntegralFunctional opaque; analyticOfCurve still a stub
TraceDegree                  0 / 3           pullbackForms / traceForms / analyticDegree all opaque
                          ────────
Substantive total            8 / 20  (40%)   excludes 2 Inventory metadata items
```

```text
Aristotle status — 1 packet per sorry per PROMPT.md §3 (currently rolling out)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active 1:1-targeted packets (covers 13 of 20 sorries)
  bbe527bb   AnalyticDegree → analyticPushforward_analyticPullback (anti-hack #4)
  c7feba63   CompactRiemannSurface → holomorphicOneForm_montel
  d8fd495f   ULiftTransport → complexTorusULift_contMDiff_up
  2bd5f151   ULiftTransport → complexTorusULift_contMDiff_down
  b4029f72   PullbackBasis → analyticPullback_id_apply
  c910ac80   PullbackBasis → analyticPullback_contMDiff
  27c56154   PullbackBasis → analyticPullback_comp_apply
  f280ecc6   PushforwardBasis → analyticPushforward_contMDiff
  271cc21e   PushforwardBasis → analyticPushforward_id_apply
  6c796045   PushforwardBasis → analyticPushforward_comp_apply
  3d5f379e   AnalyticOfCurveBasis → pathIntegralFunctional_self
  c6c4c612   AnalyticOfCurveBasis → analyticOfCurve_contMDiff
  4f76ac75   AnalyticOfCurveBasis → pathIntegralFunctional_separates_points (Abel)

Active infrastructure packet
  8585f085   Banach-data Step 4 (SectionComplete.lean, NEW). Builds toward
             holomorphicOneForm_normedSpace_uniformOnCompact.

Sorries pending packets (7 remaining; Aristotle hit max-concurrent-jobs limit)
  PeriodFunctional: 2 sorries (rate-limited)
  GenusZeroClassification: 4 sorries (rate-limited)
  CompactRiemannSurface: holomorphicOneForm_normedSpace_uniformOnCompact
                          (waits on 8585f085 → SectionComplete first)

Cancelled earlier this tick (bundled, replaced by 1:1 above)
  7e2bc288, 4d56b249, d1d10391, d967438b, c5101910, b3280ab0

Recent integrations
  51fd0fce   SectionMetric (Step 3) — dist + 4 MetricSpace axioms, sorry-free
  f1786fa8   SectionSupNorm (Step 2) — supNorm + 5 properties, sorry-free
  63158306   SectionFiberNorm (Step 1) — fiberNorm + continuity, sorry-free
  90750074   Liouville-core split (structure improved)
  6992e390   Translation-invariance reduction in CompactRiemannSurface
  5dfd5106   Montel survey + Blocker 5 finding
  848a0c88   SectionTopologyConstructionRecon (5-step plan)

Full history in aristotle_jobs.jsonl.
```

```text
Build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass    lake build Jacobian.Challenge
Statement bank            pass    lake build Jacobian.WorkPackets.StatementBank
Periods umbrella          pass    lake build Jacobian.Periods
Solution                  pass    lake build Jacobian.Solution

Per-directory sorry-free ratios (production files)
  HolomorphicForms             27 / 29
  AnalyticJacobian             23 / 23
  AbelJacobi                   19 / 20
  TraceDegree                  81 / 84
  Periods                     171 / 173
  ComplexTorus                 47 / 53
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Step 4 (8585f085) — completeness of supNorm metric.
   When it returns, Step 5 (assembly into HolomorphicOneFormBanachData_of_compact)
   is a 10-15 LOC follow-up.
2. Liouville-core leaves in GenusZeroClassification.lean
   (_finite_eq_zero, _infty_eq_zero) — both blocked on the chart-extraction
   Mathlib gap documented in ChartCoeffExtractionRecon.lean.
3. The TraceDegree, ULiftTransport, and AnalyticOfCurveBasis sorries
   are all in scope (no off-limits partition besides Challenge.lean).
```

## About

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
