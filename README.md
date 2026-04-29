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

Last tick: 2026-04-29 02:25 EDT

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 127        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  391 / 397    counting `:= sorry`-ending lines per file. 6 files with
                                          real sorries — see below. (412 total .lean − 15 design
                                          files: Challenge, Solution, StatementBank, *Recon*.)

Reproduction: for f in <files>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
Open sorries by file (all production sorries; 6 files, 17 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface   3   fiberNorm_continuous +
                                               supNorm_cauchySeq_tendsto +
                                               closedBall_totallyBounded
  HolomorphicForms/GenusZeroClassification 6   coeff_entire (NEW from 76c01cf9) +
                                               coeff_tendsto_zero (NEW from 76c01cf9) +
                                               infty Liouville leaf +
                                               subsingleton_holomorphicOneForm_of_homeo_sphere (NEW from 88effa1c) +
                                               genus_zero_homeomorph_onePointCx
                                               (originals onePointCx_toFun_finite_eq_zero and
                                                holomorphicOneFormLinearEquivOfHomeoSphere are now
                                                sorry-free assemblies)
  Periods/PeriodFunctional                 3   periodSubgroup_isZLattice +
                                               symplectic_basis_of_cycles (NEW from 0cfa1878) +
                                               period_vectors_linearIndependent_of_symplectic (NEW from 0cfa1878)
                                               (periodVectors_linearIndependent now sorry-free assembly)
  AbelJacobi/AnalyticOfCurveBasis          1   Abel-injectivity (separates_points)
  TraceDegree/PullbackBasis                2   basisDualPullback (id, comp) — comp now has substantive
                                               blocker docstring (ad278fcd)
  TraceDegree/PushforwardBasis             2   pushforwardTraceLift_apply_at (id, comp)
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
This tick: 4 Aristotle integrations (clean TOPDOWN splits + 1 blocker docstring):
  76c01cf9 (Liouville finite split into 2), 88effa1c (LinearEquivOfHomeoSphere
  reduced to 1), 0cfa1878 (periodVectors_linearIndependent split into 3),
  ad278fcd (basisDualPullback_comp blocker analysis).
  5 new packets submitted for the new sub-obligation sorries
  (dc2c19e1, 659de1fb, af6e2c7a, e227f244, 0de5af2a).
  2 replacement sub-agents launched (a68119d2, af653549) after a7498d24
  was killed and abcfd3e5 returned redundant docstring expansion.

Active our-packets — covering current sorries
  de8822fb   CompactRiemannSurface → fiberNorm_continuous (IN_PROGRESS 13%)
  8a8ea66d   CompactRiemannSurface → closedBall_totallyBounded (IN_PROGRESS 13%)
  706bf2e2   CompactRiemannSurface → supNorm_cauchySeq_tendsto (IN_PROGRESS 13%)
  03715a4d   GenusZero → Liouville leaves
  6b2f47f1   AnalyticOfCurveBasis → separates_points
  0a5f74a8   PeriodFunctional → range/isZLattice
  05100f76   PullbackBasis → basisDualPullback_id
  ba57741f, dc58e548   PushforwardBasis _id_apply_at, _comp_spec_apply_at
                        — both integrated as blocker docstrings;
                        sorries persist awaiting structural Mathlib trace work

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
CompactRiemannSurface          pass               lake build (110s, 3 sorries)
PushforwardBasis               pass               lake build (33s, 2 sorries)
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Watch in-flight Aristotle packets: 8a8ea66d, 706bf2e2, de8822fb.
2. The 4 PushforwardBasis sorries are now well-documented (ba57741f +
   dc58e548) but the structural fix (concrete traceMap) is a
   substantial Mathlib-infrastructure project — defer.
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
