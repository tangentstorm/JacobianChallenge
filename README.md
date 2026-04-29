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

Last tick: 2026-04-29 00:25 EDT

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 122        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  391 / 397    counting `:= sorry`-ending lines per file. 6 files with
                                          real sorries — see below. (412 total .lean − 15 design
                                          files: Challenge, Solution, StatementBank, *Recon*.)

Reproduction: for f in <files>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
Open sorries by file (all production sorries; 6 files, 14 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface   3   fiberNorm_continuous +
                                               supNorm_cauchySeq_tendsto (NEW: subagent a8db8a8f split;
                                                supNorm_completeSpace now sorry-free assembly) +
                                               closedBall_totallyBounded (NEW: Aristotle 20995679 split;
                                                montel_subseq_isCauchy and _subseq_tendsto now
                                                sorry-free assemblies)
  HolomorphicForms/GenusZeroClassification 4   finite/infty Liouville leaves +
                                               uniformization-lite (holomorphicOneFormLinearEquivOfHomeoSphere) +
                                               deep uniformization (genus_zero_homeomorph_onePointCx)
  Periods/PeriodFunctional                 2   ZLattice integrality + Riemann-bilinear lin-indep
                                               (split via PeriodSpanHelpers helper file)
  AbelJacobi/AnalyticOfCurveBasis          1   Abel-injectivity (separates_points)
  TraceDegree/PullbackBasis                2   basisDualPullback (id, comp)
  TraceDegree/PushforwardBasis             2   pushforwardTraceLift_apply_at (id, comp) — pointwise form
  -----------------------------------------
  HolomorphicForms/CompactRiemannSurface   ↑   _normedSpace_uniformOnCompact DISCHARGED this tick (Step 5
                                               assembly via Aristotle 58eb31f0 partial integration)
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
Aristotle status — 14 production sorries, all covered by ≥ 1 packet
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Rejected this tick (1)
  bed365ae   Original supNorm_completeSpace packet — stale baseline
             (predates a8db8a8f subagent + 20995679 Montel TOPDOWN).
             Returns no proof, just a blocker docstring + destructive
             Montel revert. Net 0 effect on main.

Active our-packets — covering current sorries
  ba57741f   PushforwardBasis → pushforwardTraceLift_id_apply_at (IN_PROGRESS 17%)
  de8822fb   CompactRiemannSurface → fiberNorm_continuous (IN_PROGRESS 13%)
  8a8ea66d   CompactRiemannSurface → closedBall_totallyBounded (IN_PROGRESS 1%)
  706bf2e2   CompactRiemannSurface → supNorm_cauchySeq_tendsto (IN_PROGRESS 3%)
  03715a4d   GenusZero → Liouville leaves
  6b2f47f1   AnalyticOfCurveBasis → separates_points
  0a5f74a8   PeriodFunctional → range/isZLattice
  05100f76   PullbackBasis → basisDualPullback_id

Stale: e7250841 (rejected last tick), bed365ae (rejected this tick),
  dc58e548 (integrated), 20995679 (integrated).

Sub-agent in flight: a5920caf (was racing now-discharged subseq_isCauchy;
  result will be evaluated against the new closedBall_totallyBounded
  sorry on completion).

Active our-packets — covering current sorries
  e7250841   COMPLETED, REJECTED this tick (stale baseline pre-Step5/Montel)
  03715a4d   GenusZero → Liouville leaves (one of 4)
  6b2f47f1   AnalyticOfCurveBasis → separates_points
  0a5f74a8   PeriodFunctional → range/isZLattice
  05100f76   PullbackBasis → basisDualPullback_id
  ba57741f   PushforwardBasis → pushforwardTraceLift_id_apply_at
  dc58e548   PushforwardBasis → pushforwardTraceLift_comp_spec_apply_at
  de8822fb   CompactRiemannSurface → fiberNorm_continuous
  bed365ae   CompactRiemannSurface → supNorm_completeSpace
  20995679   CompactRiemannSurface → montel_subseq_isCauchy (NEW)

Active infrastructure packet
  8585f085   Banach-data Step 4 (SectionComplete.lean) — feeds bed365ae.

Full history in aristotle_jobs.jsonl.
```

```text
Build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Last commit (0e02ade)          unverified         lake stalled past 10-min capture window
                                                   (structural assemblies via Tendsto.cauchySeq +
                                                   Metric.complete_of_cauchySeq_tendsto; verify next tick)
This tick                      no Lean changes    bookkeeping only (bed365ae rejected)
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Verify last commit (0e02ade) builds clean.
2. Watch in-flight Aristotle packets: 8a8ea66d (closedBall_totallyBounded),
   706bf2e2 (supNorm_cauchySeq_tendsto), de8822fb (fiberNorm_continuous),
   ba57741f (pushforwardTraceLift_id_apply_at).
3. Liouville-core leaves in GenusZeroClassification.lean — blocked on the
   chart-extraction Mathlib gap.
4. PullbackBasis basisDualPullback_id / _comp — revisit with a richer bundle.
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
