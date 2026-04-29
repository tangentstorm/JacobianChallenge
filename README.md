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

Last tick: 2026-04-28 23:30 EDT

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 120        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  391 / 397    counting `:= sorry`-ending lines per file. 6 files with
                                          real sorries — see below. (412 total .lean − 15 design
                                          files: Challenge, Solution, StatementBank, *Recon*.)

Reproduction: for f in <files>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
Open sorries by file (all production sorries; 6 files, 14 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface   3   fiberNorm_continuous (NEW Step 5 split) +
                                               supNorm_completeSpace (NEW Step 5 split, awaits 8585f085) +
                                               montel_subseq_tendsto (existing)
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
Integrated this tick (1, partial)
  58eb31f0   CompactRiemannSurface Step 5 assembly only. Rejected the
             packet's destructive Montel revert (stale baseline pre-e833f04).
             Net +1 sorry (1 → 2 in CompactRiemannSurface): original
             _normedSpace_uniformOnCompact is now sorry-free assembly with
             named sub-obligations holomorphicOneForm_fiberNorm_continuous and
             holomorphicOneForm_supNorm_completeSpace.

New packets submitted this tick (2)
  de8822fb   holomorphicOneForm_fiberNorm_continuous (NEW Step 5 sub-obligation)
  bed365ae   holomorphicOneForm_supNorm_completeSpace (NEW; awaits 8585f085)

Active our-packets — covering current sorries
  e7250841   CompactRiemannSurface → montel_subseq_tendsto (IN_PROGRESS 15%)
  03715a4d   GenusZero → Liouville leaves (one of 4)
  6b2f47f1   AnalyticOfCurveBasis → separates_points
  0a5f74a8   PeriodFunctional → range/isZLattice
  05100f76   PullbackBasis → basisDualPullback_id
  ba57741f   PushforwardBasis → pushforwardTraceLift_id_apply_at
  dc58e548   PushforwardBasis → pushforwardTraceLift_comp_spec_apply_at
  de8822fb   CompactRiemannSurface → fiberNorm_continuous (NEW)
  bed365ae   CompactRiemannSurface → supNorm_completeSpace (NEW)

Active infrastructure packet
  8585f085   Banach-data Step 4 (SectionComplete.lean) — feeds bed365ae.

Pending sub-agent integration (next tick)
  Montel subseq_tendsto TOPDOWN split (a7b046e5b69cfb1ea worktree).
    Splits subseq_tendsto sorry → subseq_isCauchy sorry + sorry-free
    Banach-completeness wrapper. Defer to keep diff small.

Full history in aristotle_jobs.jsonl.
```

```text
Build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CompactRiemannSurface         pass               lake build Jacobian.HolomorphicForms.CompactRiemannSurface
Previous tick combined        pass (post-fact)   lake build Jacobian.HolomorphicForms.GenusZeroClassification
                                                   Jacobian.Periods.PeriodFunctional
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Integrate the Montel subagent's TOPDOWN split (worktree
   a7b046e5b69cfb1ea) — converts subseq_tendsto sorry into
   subseq_isCauchy sorry + sorry-free Banach-completeness wrapper.
2. Aristotle e7250841 (Montel subseq_tendsto, IN_PROGRESS 15%) — when it
   completes, evaluate against the subagent's split.
3. PushforwardBasis _apply_at sorries — packets ba57741f / dc58e548 in flight.
4. Liouville-core leaves in GenusZeroClassification.lean — blocked on the
   chart-extraction Mathlib gap.
5. PullbackBasis basisDualPullback_id / _comp — revisit with a richer bundle.
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
