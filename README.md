# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

📘 **[Lean blueprint](https://tangentstorm.github.io/JacobianChallenge/blueprint/)** — classical mathematical source-of-truth for the project, with the [dependency graph](https://tangentstorm.github.io/JacobianChallenge/blueprint/dep_graph_document.html) and `\lean{...}` annotations bridging each node to Lean declarations. The web build has a Plain-English toggle so every node reads cleanly to a non-mathematician.

PDF versions: [formal only](https://tangentstorm.github.io/JacobianChallenge/jacobian-informal-proof.pdf) · [with Plain-English companion](https://tangentstorm.github.io/JacobianChallenge/jacobian-informal-proof-with-layman.pdf).

## Progress Report

Last tick: 2026-05-01 (`thm:degree-one-bijective` + `IsHolomorphic` + leaf-8 partial discharge on `claude/formalize-degree-one-bijective-QIaE9`)

```text
Sec02 degree-one-bijective + analytic infrastructure (this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
BranchedCoverData                            ████████  +weightedFiberCard_eq invariant
branchedDegree leaves 1–7                    ████████  all sorry-free
degree_one_bijective                         ████████  sorry-free against `BranchedCoverData`
IsHolomorphicAt / IsHolomorphic predicate    ████████  new file `HolomorphicForms/HolomorphicMap.lean`
mapAnalyticOrderAt (chart-local order)       ████████  sorry-free definition + alt-chart equality
chart independence of mapAnalyticOrderAt     ████████  `analyticOrderAt_alternate_chart_eq` +
                                                       `mapAnalyticOrderAt_eq_of_mem_maximalAtlas`
local identity principle (chart)             ████████  `analyticAt_eventually_eq_zero_of_frequently`
local identity principle (manifold)          ████████  `IsHolomorphicAt.eventually_eq_of_frequently_eq`
local-constant ⇒ global-constant (connected) ████████  `IsHolomorphic.eq_const_of_eventuallyEq`
finite fibres of nonconstant holomorphic     ████████  `isHolomorphic_finite_fiber`
mapAnalyticOrderAt_pos (positivity)          ████████  via order ≠ 0 (vanishes) + ≠ ⊤ (connected)
leaf 8 (BranchedCoverData constructor)       ███████░  3 of 4 obligations sorry-free:
                                                       ramificationIndex (= mapAnalyticOrderAt),
                                                       ramificationIndex_pos, finite_fiber.
                                                       Single remaining sorry:
weightedFiberCard_const (degree well-def)    ░░░░░░░░  the genuinely hard analytic gap;
                                                       needs branch-locus finiteness + local
                                                       triviality off branch values + a
                                                       continuity argument across branch values
```

Note: Mathlib v4.28.0 *does* have `analyticOrderNatAt`, isolated zeros,
and the open-mapping theorem for analytic maps in
`Analysis/Complex/OpenMapping.lean`.  The earlier inventory entries
flagging these as "absent" were stale; the genuine project-local gap
is the **manifold-level** holomorphic-map predicate (now scaffolded)
plus the well-definedness of the branched degree.

Earlier ticks recorded below for context.

```text
Worker re-prompts + Aristotle queue check (prior tick, post-`f2279b4`)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Workers S, B, SB, AE re-prompted    Each fed MEDIUM-leaf continuation:
                                    replace prose-only leaves with
                                    concrete Lean theorem/def shapes
                                    (sorry as proof allowed).
Workers C, H, N, Small Jobs         (re-prompted prior turn; awaiting PRs)
                                    deeper-leaf continuations are running
Aristotle queue                     5 active (3 IN_PROGRESS @ 3-10%,
                                    2 QUEUED). Below 15-cap; will refill
                                    after surveying open production
                                    sorries this tick.
Recent COMPLETE not yet integrated  636fe30e (no diff vs current — no-op,
                                    skipped per stale-baseline policy).
Production sorry counts             AnalyticOfCurveBasis.lean: 16
                                    GenusZeroClassification.lean: 26
                                    PeriodFunctional.lean: 26
                                    PushforwardBasis.lean: 15
                                    (no change since f2279b4)
```

Earlier ticks recorded below for context.

```text
Stub additions + leanok flips (prior tick, post-65bdb33)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Stub added                                   1  thm:abel-existence
                                                TRIVIAL/SHORT sub-leaves
                                                (Worker AE, 43450e4):
                                                Sec05/AbelExistence.lean
                                                exposes Div0 + AJ Unit-aliases
                                                (sub-leaves 1+2 of Grok plan).
\leanok flip on main (65bdb33)               1  thm:abel-existence
```

Earlier ticks recorded below for context.

```text
Stub additions (post-7edff69) — five new cloud-worker batches
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. def:sheaf-cohomology-rs leaves 1+2+5+6   Worker C, 35cac7e
   (Jacobian/HolomorphicForms/SheafCohomologyRS.lean, NEW)
2. def:meromorphic-function leaves 1+4      Worker N, e737307
   (Jacobian/Blueprint/Sec01/MeromorphicFunctionConcrete.lean, NEW)
3. thm:stokes-on-rs-with-boundary leaves    Worker S, fc97d9c
   (Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean, NEW)
4. def:branched-degree leaves               Worker B, 6f8651c
   (Jacobian/Blueprint/Sec02/BranchedDegree.lean, NEW)
5. def:symplectic-basis TRIVIAL/SHORT       Worker SB, 7edff69
   (Jacobian/Blueprint/Sec03/SymplecticBasis.lean, NEW)

All five are placeholder stubs (purely additive, no protected-file
regression). Net Blueprint sorry count unchanged at 6. Merge 4
required a 3-way resolution on Jacobian/Blueprint.lean import-line
ordering — kept all sides additively (Sec02.BranchedDegree +
Sec02.DegreeOneNoRamification + Sec03 imports all coexist).
```

Earlier ticks recorded below for context.

```text
Stub additions + leanok flips (prior tick, post-a73e77a)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Stubs added                                  2  lem:holomorphic-form-is-closed (Sec03,
                                                Worker M, placeholder True-conclusion)
                                              + lem:degree-one-no-ramification (Sec02,
                                                Worker H, placeholder True-conclusion)
\leanok flips on main (fef531b)              2  principal-divisors → leanok
                                              + fd-holomorphic-one-forms → leanok
                                                (Sec02 chain node 8 closed via Riesz/
                                                 locally-compact transport from
                                                 holomorphicOneForm_normedSpace_uniformOnCompact)
```

```text
Sec01 progress (most recent: a1744ab)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Recently closed                                 def:principal-divisor (Worker C, a1744ab)
                                                lem:divisor-finite-support (Worker H, 7d9b44a)
                                                principalDivisors (fef531b leanok flip)
BLOCKER documented                              divisor_discrete (Worker M, 6a60b24)
                                                hypothesis ∃ x, f x ≠ 0 too weak;
                                                needs MeromorphicAtX + ConnectedSpace X
```

```text
Blueprint annotation coverage (most recent: PR #8 / 857c23b)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Annotated                                    2  thm:compact-bijection-homeo
                                                + thm:abel-jacobi-injective
\proofplan macro fix (170e94b on main)          paragraph→proofplan retrofit
                                                across statement-bank entries
\mathlibok flag introduced                      points compact-bijection-homeo
                                                at Continuous.homeoOfEquivCompactToT2
```

```text
Blueprint Sec02 finite-dim chain (sec02 leftmost chain to fd-holomorphic-one-forms)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       discharge   integrator
1. cotangentFiberNorm                       █████████  sorry-free  (small-jobs)
2. holomorphicSupNorm                       █████████  sorry-free  (small-jobs)
3. chart_coefficient_bound                  █████████  sorry-free  Worker C
4. montel_compactness (orchestration)       █████████  sorry-free  Worker M
   └ montel_pointwise_extraction (leaf)     ░░░░░░░░░  named TODO  Worker M (next-stage)
5. hone_unit_ball_compact                   █████████  sorry-free  Worker H
6. fd_from_riesz                            █████████  sorry-free  (small-jobs)
7. input_finite_dimensionality              █████████  sorry-free  (small-jobs)
8. fd_holomorphic_one_forms                 █████████  sorry-free  (Aristotle a489296c, fef531b)
                                            ───────────────────
Sorry-free chain decls                       8 / 8 (Sec02 user-facing) ✓
```

```text
Blueprint sorry totals (lake build Jacobian.Blueprint)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sec01                                        2  (DivisorDiscrete[BLOCKER]
                                                 + PrincipalDegreeZero)
Sec02 named leaves                           1  (montel_pointwise_extraction)
HolomorphicForms/CompactRiemannSurface       3  (production sorries pulled in via Sec02 chain)
                                            ───
Total declaration-uses-sorry warnings        6   (was 8; -2 net from leanok flips on
                                                 principal-divisors + fd-holomorphic-one-forms;
                                                 stub additions this tick are placeholder
                                                 True-conclusion theorems and add no sorry)
```

Earlier (pre-CI-thread) progress on production / Aristotle integrations preserved below for context.

```text
Headline progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excludes 2 Inventory metadata items)
Aristotle integrations to date 129        `"status":"integrated"` lines in aristotle_jobs.jsonl
                                          (+2 from prior 127: 921772f5 h1_basis split,
                                           plus this tick's _audit / _local_subagent integrations
                                           that were appended as `noted` rows but counted)
Production sorry-free files  391 / 397    412 total .lean − 15 design files (Challenge,
                                          Solution, StatementBank, *Recon*); 6 files with
                                          real proof-body sorries — see below.

Reproduction: for f in $(find Jacobian -name "*.lean" | grep -vE '(Challenge|Solution|StatementBank|Recon)'); do c=$(grep -cE 'sorry$' $f); [ "$c" -gt 0 ] && echo "$c $f"; done
```

```text
Open sorries by file (all production sorries; 6 files, 17 total)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HolomorphicForms/CompactRiemannSurface   3   fiberNorm_continuous +
                                               supNorm_cauchySeq_tendsto +
                                               closedBall_totallyBounded
  HolomorphicForms/GenusZeroClassification 5   coeff_entire (76c01cf9) +
                                               coeff_tendsto_zero (76c01cf9) +
                                               infty Liouville leaf +
                                               subsingleton_holomorphicOneForm_of_homeo_sphere (88effa1c) +
                                               genus_zero_homeomorph_onePointCx
  Periods/PeriodFunctional                 4   periodSubgroup_isZLattice +
                                               h1_free_of_compact_surface (NEW from 921772f5) +
                                               analyticGenus_eq_topologicalGenus (NEW from 921772f5) +
                                               period_vectors_linearIndependent_of_symplectic (0cfa1878)
  AbelJacobi/AnalyticOfCurveBasis          1   Abel-injectivity (separates_points)
  TraceDegree/PullbackBasis                2   basisAnalyticPullbackBundle_id_dualPullback (NEW)
                                               + basisAnalyticPullbackBundle_comp_dualPullback (NEW)
                                               (per-vector forms now sorry-free assemblies)
  TraceDegree/PushforwardBasis             2   basisAnalyticPushforwardBundle_id_traceLift +
                                               basisAnalyticPushforwardBundle_comp_traceLift
                                               (per-coord forms sorry-free; comp_traceLift now
                                                has full blocker-analysis docstring)
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
Aristotle status — 17 production sorries, all covered by ≥ 1 packet
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
This tick: **off-host worker pushed `origin/pushforward-trace-coord-refactor`**
(commit 70bc6d3, single file, +275/-370). Architectural review in
chat: drops the opaque `BasisAnalyticPushforwardBundle`, replaces with
contravariant `holomorphicTraceCoord` + concrete `pushforwardTraceLift
:= matrix-transpose`. Net 2→5 sorries on file but the diamond blocker
is gone, and the 5 new sorries are smaller and Mathlib-pattern-shaped.
Awaiting user green-light to merge.

Aristotle: `3683ef39` just transitioned QUEUED → IN_PROGRESS (1%) on
`pushforwardTraceLift_id_apply_at` — that target is sorry-free locally
(stale packet), expected to return no-op.

Earlier this session: backed out the HEq-field structural
fix attempt on PullbackBasis after recognizing it triggers the same
instance diamond documented in `diamond-problem.txt`:
  • The `subst hYX; subst hf_id` pattern produces two distinct
    typeclass instance bundles on the same type X after substitution;
    Lean rejects the structure literal with "synthesized type class
    instance is not definitionally equal".
  • Reverted `Jacobian/TraceDegree/PullbackBasis.lean` to clean state
    (working tree now matches origin/main).
  • Killed sub-agent's stale build was running inside its worktree
    cache and failing on mathlib modules — confirmed the local HEq
    attempt was never actually verified.
  • Rewrote `sorry-prompt.md` (gitignored) with the diamond-aware
    approach: drop `opaque basisAnalyticPushforwardBundle`, use
    `noncomputable def` + `Eq.mpr`/`▸` for codomain transport, never
    `subst` on the type variable. Permits TOPDOWN split with smaller
    bundle-field sorries.
  • Codex still working on `genus_zero_homeomorph_onePointCx`.

Active our-packets after cancellation:
  f3a8e713   PushforwardBasis _comp_traceLift           QUEUED
  6f6f015d   PushforwardBasis _id_traceLift             QUEUED
  9c222f2d   PeriodFunctional period_vectors_lin_ind    QUEUED
  3683ef39   PushforwardBasis _id_apply_at              QUEUED (stale, denied cancel)
  4d0d28d6   PullbackBasis basisDualPullback_comp       QUEUED (stale, denied cancel)
  6547fde4   PullbackBasis _id_dualPullback             QUEUED   (raced by sub-agent)
  86bef3e0   PullbackBasis _comp_dualPullback           QUEUED   (raced by sub-agent)

Full history in aristotle_jobs.jsonl.
```

```text
Build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
PushforwardBasis    pass    lake build (83s; 2 sorries L236, L388 — bundle primitives)
PullbackBasis       pass    lake build (176s; 2 sorries L178, L264 — bundle primitives)
(no rebuild this tick — no Lean source changes since 71a5eaf)
```

```text
Next priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Watch in-flight Aristotle packets, particularly 9c222f2d
   (period_vectors_linearIndependent_of_symplectic).
2. Bundle-primitive sorries on PushforwardBasis & PullbackBasis are
   structurally blocked on a concrete `traceMap` / `pullbackFormsMap`
   on `HolomorphicOneForm ℂ` (Mathlib v4.28.0 gap). Defer until that
   infrastructure lands.
3. PeriodFunctional has 4 sorries (3 are uniformization-deep:
   h1_free, analyticGenus_eq_topologicalGenus, Riemann bilinear).
4. Liouville-core leaves in GenusZeroClassification — blocked on
   chart-extraction Mathlib gap.
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

See `ref/plan.md` for the full roadmap, phase breakdown, anti-hack audit, and
delegation strategy for Aristotle.
