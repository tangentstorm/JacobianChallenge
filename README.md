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

Last tick: 2026-04-28 23:05 EDT

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 119        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  391 / 397    counting `:= sorry`-ending lines per file. 6 files with
                                          real sorries — see below. (412 total .lean − 15 design
                                          files: Challenge, Solution, StatementBank, *Recon*.)

Reproduction: for f in <files>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
Open sorries by file (all production sorries; 6 files, 13 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface   2   Banach data + montel_subseq_tendsto
  HolomorphicForms/GenusZeroClassification 4   finite/infty Liouville leaves +
                                               uniformization-lite (holomorphicOneFormLinearEquivOfHomeoSphere) +
                                               deep uniformization (genus_zero_homeomorph_onePointCx)
  Periods/PeriodFunctional                 2   ZLattice integrality + Riemann-bilinear lin-indep
                                               (split via PeriodSpanHelpers helper file)
  AbelJacobi/AnalyticOfCurveBasis          1   Abel-injectivity (separates_points)
  TraceDegree/PullbackBasis                2   basisDualPullback (id, comp)
  TraceDegree/PushforwardBasis             2   pushforwardTraceLift_apply_at (id, comp) — pointwise form
  -----------------------------------------
  ComplexTorus/ULiftTransport              0   contMDiff_up/down DISCHARGED this tick (subagent)
  TraceDegree/AnalyticDegree               0   anti-hack #4 closed via PullbackBundle.trace_pullback_spec
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
Aristotle status — 13 production sorries, all covered by ≥ 1 packet
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Backend ALIVE this tick — queue draining; 6 of our packets COMPLETE.

Integrated this tick (3)
  fbfe1498   GenusZero L591 sphere homeo TOPDOWN split (sorry-free assembly +
             1 deep uniformization sorry + 1 sorry-free Mathlib stereographic helper)
  360a05bf   GenusZero L320 analyticGenus eq TOPDOWN split (sorry-free assembly +
             1 sorry on holomorphicOneFormLinearEquivOfHomeoSphere)
  bbca4cae   PeriodFunctional spans_real TOPDOWN split (added sorry-free
             Jacobian/Periods/PeriodSpanHelpers.lean + 1 Riemann-bilinear sorry on
             periodVectors_linearIndependent + sorry-free assembly)

Rejected this tick (2)
  5f052643   PushforwardBasis comp_spec — zero-placeholder regression (paper-over)
  403c9581   PullbackBasis basisDualPullback_comp — destructive bundle refactor
             would have removed fields needed by AnalyticDegree anti-hack #4
  e19361c4   GenusZero (Aristotle's pick) — duplicate of fbfe1498 (skipped)

Subagent-integrated this tick (worktree-isolated)
  ULiftTransport contMDiff_up + _down — substantive proofs (Claude fixed two
    .symm direction errors). Net −2 sorries (15 → 13).
  PushforwardBasis TOPDOWN refinement — _id_apply / _comp_spec_apply now
    sorry-free assemblies on smaller per-coordinate _apply_at sorries.

Active our-packets (after this tick) — covering open sorries
  e7250841   CompactRiemannSurface → montel_subseq_tendsto (IN_PROGRESS 5%)
  58eb31f0   CompactRiemannSurface → normedSpace_uniformOnCompact (IN_PROGRESS 27%)
  03715a4d   GenusZero → Liouville leaves (one of 4)
  6b2f47f1   AnalyticOfCurveBasis → separates_points
  0a5f74a8   PeriodFunctional → range/isZLattice
  05100f76   PullbackBasis → basisDualPullback_id
  ba57741f   PushforwardBasis → pushforwardTraceLift_id_apply_at (NEW)
  dc58e548   PushforwardBasis → pushforwardTraceLift_comp_spec_apply_at (NEW)

Active infrastructure packet
  8585f085   Banach-data Step 4 (SectionComplete.lean) — feeds 58eb31f0.

Stale packets (target sorry no longer exists; left running per memory rule):
  d8fd495f, 2bd5f151, b7799fc9, 5f052643, 7f3ec297, e3dcd529, 654d5071,
  f914a263, 65001239, c69fcd88, 369f3f7b, 16277f52, bbe527bb, c7feba63,
  b4029f72, c910ac80, 27c56154, f280ecc6, 271cc21e, 6c796045, 3d5f379e,
  c6c4c612.

Sub-agents launched this tick (worktree, racing Aristotle's back of queue)
  GenusZero L591 sphere homeo (raced fbfe1498 — Aristotle won; subagent's
    parallel-equivalent edit not merged)
  Montel subseq_tendsto (still running, racing e7250841)

Full history in aristotle_jobs.jsonl.
```

```text
Build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target              not run this tick   lake build Jacobian.Challenge
Statement bank                not run this tick   lake build Jacobian.WorkPackets.StatementBank
GenusZeroClassification       pass               lake build Jacobian.HolomorphicForms.GenusZeroClassification
ULiftTransport                pass               lake build Jacobian.ComplexTorus.ULiftTransport
PushforwardBasis              pass               lake build Jacobian.TraceDegree.PushforwardBasis
PeriodSpanHelpers (NEW)       pass               lake build Jacobian.Periods.PeriodSpanHelpers
PeriodFunctional              in flight          lake build Jacobian.Periods.PeriodFunctional
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Wait on Montel subagent (a7b046e5b69cfb1ea) and Aristotle e7250841 — whichever
   wins the race for `holomorphicOneForm_montel_subseq_tendsto`.
2. PushforwardBasis _apply_at sorries — packets ba57741f / dc58e548 in flight;
   bundle-incompatibility blocker documented in file docstring.
3. Liouville-core leaves in GenusZeroClassification.lean (existing) — still
   blocked on the chart-extraction Mathlib gap documented in
   `ChartCoeffExtractionRecon.lean`.
4. PullbackBasis basisDualPullback_id / _comp — Aristotle's 403c9581 was
   destructive (bundle field removal); revisit with a richer bundle approach.
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
