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

Last tick: 2026-04-28 13:12 EDT

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
Open sorries by file (all production sorries; 7 files, 15 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface  2   Banach data + montel_subseq_tendsto (Montel split via TOPDOWN by subagent)
  HolomorphicForms/GenusZeroClassification 4  finite/infty Liouville leaves +
                                              uniformization-lite + hard-direction unif.
  Periods/PeriodFunctional                2   IsZLattice integrality + Riemann-bilinear nondegeneracy
  AbelJacobi/AnalyticOfCurveBasis         1   Abel-injectivity (separates_points)
  ComplexTorus/ULiftTransport             2   ULift transition obligations
  TraceDegree/PullbackBasis               2   basisDualPullback (id, comp); mk_eq/contMDiff/degree/trace_pullback via bundle
  TraceDegree/PushforwardBasis            2   pushforwardTraceLift (id, comp_spec); other axioms via bundle
  TraceDegree/AnalyticDegree              0   anti-hack #4 closed via PullbackBundle.trace_pullback_spec
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
Aristotle status — 1:1 packet/sorry coverage now complete (15/15)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active packets covering current sorries (15 / 15)
  e7250841   CompactRiemannSurface → holomorphicOneForm_montel_subseq_tendsto (NEW this tick)
  58eb31f0   CompactRiemannSurface → holomorphicOneForm_normedSpace_uniformOnCompact
             (Step 5 assembly; depends on 8585f085 → SectionComplete first)
  03715a4d   GenusZeroClassification → finite/infty Liouville leaves (generic)
  e19361c4   GenusZeroClassification → Aristotle's pick (1:1 orphan coverage)
  360a05bf   GenusZeroClassification → analyticGenus_eq_of_homeomorphic_sphere (L320)
  fbfe1498   GenusZeroClassification → sphere homeomorph (L591)
  0a5f74a8   PeriodFunctional → first sorry (isZLattice / spans_real)
  bbca4cae   PeriodFunctional → second sorry
  6b2f47f1   AnalyticOfCurveBasis → pathIntegralFunctional_separates_points (Abel)
  d8fd495f   ULiftTransport → complexTorusULift_contMDiff_up
  2bd5f151   ULiftTransport → complexTorusULift_contMDiff_down
  05100f76   PullbackBasis → basisDualPullback_id
  403c9581   PullbackBasis → basisDualPullback_comp
  b7799fc9   PushforwardBasis → pushforwardTraceLift_id
  5f052643   PushforwardBasis → pushforwardTraceLift_comp_spec

Active infrastructure packet
  8585f085   Banach-data Step 4 (SectionComplete.lean, NEW). Feeds 58eb31f0.

Backend status: 10 packets QUEUED (none IN_PROGRESS) ~1-3 hours;
no completions to integrate this tick.

Stale packets (target sorry no longer exists post-TOPDOWN/bundle) — leave running:
  bbe527bb (AnalyticDegree), c7feba63 (Montel monolithic), b4029f72/c910ac80/
  27c56154/f280ecc6/271cc21e/6c796045/3d5f379e/c6c4c612 (older Pullback/
  Pushforward/AnalyticOfCurve names). Per memory: only cancel if Claude has
  done that exact work locally; here the work was reorganized, not finished —
  let them run, results will be no-ops.

Recent integrations
  e833f04   Montel TOPDOWN split (subagent) — _subseq_tendsto + _norm_le
  51fd0fce  SectionMetric (Step 3); f1786fa8 SectionSupNorm (Step 2);
  63158306  SectionFiberNorm (Step 1)
  90750074  Liouville-core split; 6992e390 LocallyCompact translation-inv
  5dfd5106  Montel survey + Blocker 5; 848a0c88 ConstructionRecon (5-step plan)

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
