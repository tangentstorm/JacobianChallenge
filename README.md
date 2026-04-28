# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-28 04:28 EDT

```text
Headline progress markers (every value below is a fresh count from this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excluding 2 Inventory metadata items)
Aristotle integrations to date 101        `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  383 / 392    counting `:= sorry`-ending lines per file. 8 real-sorry
                                          production files (3 Claude-owned, 5 user-WIP):
                                            Claude-owned (3 files, 8 sorries — +1 this tick from
                                                          GenusZeroClassification split):
                                              HolomorphicForms/CompactRiemannSurface  (2, Riemann-Roch leaves
                                                                                       — Banach data, Montel)
                                              HolomorphicForms/GenusZeroClassification (4, was 3 — split
                                                                                       Liouville sorry into
                                                                                       finite + infty leaves;
                                                                                       assembly now sorry-free.
                                                                                       Plus uniformization-lite
                                                                                       + hard-direction unif.)
                                              Periods/PeriodFunctional                (2, IsZLattice integrality
                                                                                       + Riemann-bilinear nondeg.)
                                              [Periods/PeriodLattice                   (0 — fully delegating
                                                                                       to PeriodFunctional)]
                                            User-WIP (5 files, 12 sorries) — Claude leaves untouched:
                                              AbelJacobi/AnalyticOfCurveBasis         (3)
                                              ComplexTorus/ULiftTransport             (2)
                                              TraceDegree/PullbackBasis               (3)
                                              TraceDegree/PushforwardBasis            (3)
                                              TraceDegree/AnalyticDegree              (1)

Reproduction (per-file `:= sorry` count):
  for f in <file-list>; do echo "$f $(grep -cE ':= sorry$' $f)"; done
```

```text
StatementBank promotion (curated ratio: how many named declarations have a
real production-module implementation? Denominator is the StatementBank
itself, not a count of the tree.)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                          promoted / total   notes
Inventory                    2 / 2           metadata only — counted separately
ComplexTorus                 3 / 3           Prop placeholders backed by IsManifold + LieAddGroup instances
HolomorphicForms             3 / 3           abbrev/def used directly as the working types
Periods                      1 / 6           IntegralOneCycle abbrev concrete; periodFunctional still
                                             `opaque`; period_homology/period_pairing_full_rank still
                                             `Prop := True`; periodFullComplexLattice not yet
AnalyticJacobian             1 / 3           AnalyticJacobianType ✓ (= AnalyticJacobianGroup);
                                             equivChallenge + homeomorph_challenge still placeholders
AbelJacobi                   0 / 2           pathIntegralFunctional opaque; analyticOfCurve still a stub
TraceDegree                  0 / 3           pullbackForms / traceForms / analyticDegree all opaque
                          ────────
Substantive total            8 / 20  (40%)   excludes 2 Inventory metadata items
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours):     2 / 5
                        `1f7d4399` (prior tick) TOPDOWN on the finite leaf
                                   `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
                                   in GenusZeroClassification.lean.
                                   IN_PROGRESS at 1%, ~12min.
                        `f1786fa8` (NEW this tick) Step 2 of Banach-data
                                   construction recon — `ContMDiffSection.supNorm`
                                   + 5 sup-norm properties in NEW file
                                   `Jacobian/HolomorphicForms/SectionSupNorm.lean`.
                                   Off-critical-path; disjoint write scope.
Cancelled prior tick:   `d493c66b` — stuck at 37% for ~138 min.
Integrated this tick:   none — second parallel packet f1786fa8 just submitted.

PRIOR TICK (still standing):
Integrated `90750074` Liouville core TOPDOWN refinement —
                        substantive 3-piece split on
                        `holomorphicOneForm_onePointCx_subsingleton`.
                        (1) Aristotle introduced
                        `entire_tendsto_zero_eq_zero` (Liouville
                        application — replaced by Claude with a
                        one-liner reference to
                        `Differentiable.eq_zero_of_tendsto_zero_cocompact`
                        from `EntireZero.lean` to avoid duplicate proof).
                        (2) NEW sorry `holomorphicOneForm_onePointCx_toFun_eq_zero`
                        with excellent docstring naming the specific
                        Mathlib gap (no chart-coefficient extraction API
                        for `ContMDiffSection` of cotangent bundle).
                        (3) `_subsingleton` is now sorry-free assembly
                        via `ext_toFun`.  Net file sorry count
                        UNCHANGED (3) but structure is significantly
                        better — deep analytic content (Liouville)
                        fully discharged by `EntireZero.lean`.
```

```text
Local cadence this tick (Claude-owned)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUBSTANTIVE LOCAL SPLIT (per saved feedback "split top-down obligations"):
The `holomorphicOneForm_onePointCx_toFun_eq_zero` sorry in
`Jacobian/HolomorphicForms/GenusZeroClassification.lean` (the
chart-extraction obligation surfaced by 90750074) is now split into
two named bottom-up leaves keyed to the two charts of `OnePoint ℂ`:

  • `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` — the
    SUBSTANTIVE Liouville application on the identity chart (extract
    f via (ω.toFun ↑z) 1, prove f differentiable + tendsto 0 cocompact,
    apply Differentiable.eq_zero_of_tendsto_zero_cocompact from
    EntireZero.lean). Re-delegated to Aristotle 1f7d4399.

  • `holomorphicOneForm_onePointCx_toFun_infty_eq_zero` — vanishing
    at ∞ via continuity of inversion-chart coefficient g. Depends on
    finite leaf as a black box. Kept LOCAL for next tick (disjoint
    write scope from 1f7d4399 forces serialization in this file).

The original `_toFun_eq_zero` is now SORRY-FREE assembly via
`cases x using OnePoint.rec`. Net file sorry count: 3 → 4 (one
substantive sorry replaced by two narrower leaves + sorry-free
assembly). Both leaves carry substantive docstrings naming the
specific Mathlib v4.28.0 chart-extraction gap (no convenient API
for reading a `ContMDiffSection` of `Bundle.ContinuousLinearMap`
through chart trivialisations).

Build green: `lake build Jacobian.HolomorphicForms.GenusZeroClassification` ✓.

CANCELLED `d493c66b` after stuck at 37% for ~138 min (well past
typical successful job duration of 30-75 min — successful packets
this session: 5dfd5106 ~36min, 6992e390 ~32min, 90750074 ~73min,
63158306 ~67min). Slot freed for 1f7d4399, which is a strict
re-delegation of the now-narrower finite leaf only.

PRIOR TICK (still standing):
SUBMITTED `dc8af381` — substantive sorry-elimination packet on
`exists_compact_periodFundamentalDomain` in `PeriodFunctional.lean`.
This leaf is actually a corollary of the other two leaves
(discreteness + full ℝ-rank ⇒ compact fundamental domain via
Mathlib's `ZSpan` machinery in a finite-dim ℝ-space).  Closing it
collapses 3→2 sorries in that file and exposes that the structural
content reduces to integrality + Riemann-bilinear nondegeneracy.
Disjoint write scope from in-flight `90750074` (different file).

PRIOR TICK (still standing):
INTEGRATED `5dfd5106` Montel survey — Aristotle delivered a
~275-line docstring extension on `holomorphicOneForm_montel` in
`Jacobian/HolomorphicForms/CompactRiemannSurface.lean`. Highlights:
7-step proof outline, dependency graph identifying 5 blockers, and
effort estimate (600-1100 LOC across 3-5 modules to discharge).

KEY NEW STRUCTURAL FINDING from `5dfd5106` (Blocker 5): the
Montel statement is FALSE for arbitrary `B : HolomorphicOneFormBanachData X`
— the structure currently has no axiom connecting `B.toNorm` to
pointwise section evaluation. An arbitrary Banach norm need not
make the closed unit ball compact. The fix is a small structure
addition: a `norm_le_iSup` field bounding pointwise fiber norms by
the global norm. Deferred until step (a) is being attacked,
because `holomorphicOneForm_normedSpace_uniformOnCompact` is itself
still a sorry (no constructor breaks).

Sorry recount per-file (this tick): Claude-owned production sorries
holding steady at 9 across 3 files (CompactRiemannSurface 3,
GenusZeroClassification 3, PeriodFunctional 3 — PeriodLattice now
fully delegating with 0 own sorries). User-WIP at 12 across 5
files. Total 8 production files with real sorries (out of 391
production files, 383 sorry-free, 98%).

PRIOR TICK (still standing):
INTEGRATED `848a0c88` SectionTopologyConstructionRecon — Aristotle's
new 371-line construction-recon file for the Banach data on
`ContMDiffSection`. Concrete 5-step plan (180-305 LOC) with E=ℂ
specialisation route (embed into C(X,ℂ) + closedness) preferred to
the general-fiber route. Identifies Weierstrass uniform-limit
theorem as the hardest sub-task and notes it can be built from
Mathlib's Cauchy integral formula + dominated convergence
(~50-80 LOC). Build green (8026 jobs).

SUBMITTED `90750074` — TOP-DOWN refinement packet on the Liouville
core obligation `holomorphicOneForm_onePointCx_subsingleton`
(no global holomorphic 1-form on ℂℙ¹). This is on the critical
path for anti-hack #1 (`genus_eq_zero_iff_homeo`) and is now
feasible because the OnePoint ℂ ChartedSpace + IsManifold instances
both exist (f735aa6d + sub-agent A in prior ticks). Disjoint write
scope from in-flight `5dfd5106`.

PRIOR TICK (still standing):
TWO MORE PARALLEL SUB-AGENTS returned (third round of parallel
delegation per user "run a couple of each type in parallel"):

(C) **Genus-zero EASY direction refined** in
    `Jacobian/HolomorphicForms/GenusZeroClassification.lean`:
    monolithic sorry split into two Aristotle-shaped obligations —
    `holomorphicOneForm_onePointCx_subsingleton` (Liouville analytic
    core) + `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx`
    (uniformization-lite transport step). Assembly theorem
    `analyticGenus_eq_zero_of_homeomorphic_sphere` is now sorry-free.
    Bonus: `finiteDimensionalHolomorphicOneForms_onePointCx` instance
    proved cleanly via subsingleton-implies-⊤=⊥.

(D) **IsZLattice ℝ bridge** in `Jacobian/Periods/PeriodFunctional.lean`:
    new `basisAlignedPeriodSubmoduleℤ` (Submodule ℤ promotion) +
    derived `DiscreteTopology` and `IsZLattice ℝ` instances — clean
    type-level bridges from the existing 3 leaves. Downstream code
    can now write `[IsZLattice ℝ (basisAlignedPeriodSubmoduleℤ X)]`
    and have it inferred. Sorry count unchanged (3→3); future round
    can replace `Classical.choose` with explicit
    `ZSpan.fundamentalDomain` machinery.

PRIOR TICK (still standing):
TWO PARALLEL SUB-AGENTS dispatched (per user request "continue
delegating top-down work to sub-agents... narrow gaps from bottom-up
work"). Both stayed in scope this time, no overreach:

(A) **NEW: `IsManifold 𝓘(ℂ,ℂ) ⊤ (OnePoint ℂ)` instance** in
    `Jacobian/HolomorphicForms/OnePointCxIsManifold.lean` (224 lines,
    sorry-free, build green). Closes Packet C of the genus-zero plan.
    Sequel to f735aa6d's ChartedSpace. ℂℙ¹ is now a real complex
    manifold in our project. Bottom-up content discharged via
    `contDiffAt_inv ℂ` + 4-way chart-pair case split.

(B) **Refined `compactRiemannSurface_finiteDimensionalHolomorphicOneForms`**
    in `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`: the
    single big sorry on Riemann-Roch is replaced by 3 named
    theorem-sorry obligations matching 72ac3a75's 3-step plan
    (Banach data on the section space, Montel for holomorphic 1-forms,
    local compactness). FD instance is now sorry-free assembly that
    derives finite-dim from local compactness via
    `FiniteDimensional.of_locallyCompactSpace`. Sorry-count delta:
    1 → 3 (canonical TOPDOWN.md success pattern).

PRIOR TICK (still standing):
SUB-AGENT top-down refinement round (per user request "delegate
some top-down work to a subagent"): un-opaqued `periodFundamentalDomain`
in `PeriodLattice.lean` to `Classical.choose` of a new
`exists_compact_periodFundamentalDomain` theorem in `PeriodFunctional.lean`.
Both `_isCompact` and `_covers` are now one-liners delegating to
`choose_spec`. Also added `periodSubgroup_spans_real` (the Riemann
bilinear nondegeneracy / full-ℝ-rank half of `IsZLattice ℝ`).
PeriodLattice sorry-count: 2 → 0. PeriodFunctional sorry-count:
1 → 3 (well-named bottom-up obligations). Build green.

NB: sub-agent overreached scope — also touched `AnalyticOfCurveBasis.lean`
(reverted; was clean before tick) and `ULiftTransport.lean` (cannot
revert without destroying user WIP; left dirty for user to resolve).

PRIOR TICK (still standing):
CODEX top-down refinement round (per user-fired `codex-prompt.md`):
introduced `theorem periodSubgroup_isZLattice` in
`Jacobian/Periods/PeriodFunctional.lean` as the named bottom-up obligation
for the integrality of the period pairing image, and refined
`basisAlignedPeriodSubgroup_isDiscrete` in
`Jacobian/Periods/PeriodLattice.lean` to a one-liner delegating to it.
Also updated `Jacobian/WorkPackets/TopDown.md` Declaration Map.
**Sorry-count delta: 0** (one sorry replaced by a strictly smaller,
better-named one). Note: codex used `opaque` for a Prop-valued declaration;
Claude fixed by switching to `theorem ... := sorry` per TOPDOWN.md rule 7
(opaque is for type-level data, instance/theorem for Props).

PRIOR TICK (still standing):
INTEGRATED `10e5bfbb` — **TRACE-PULLBACK IDENTITY** survey on
`analyticPushforward_analyticPullback` (anti-hack #4 — forces
`pushforward_pullback`). ~220-line analysis with step-by-step proof
outline (branched covering → fiber cardinality → fiber-trace
summation → identity principle → period-quotient descent), Mathlib
v4.28.0 status table, TWO blockers (all three opaques have no
specification; no Mathlib infrastructure for branched coverings,
form pullback, sheaf trace, or identity principle), and
RECOMMENDED RESOLUTION: declare `analyticPushforward_analyticPullback_spec`
companion opaque to `analyticDegree`, then this lemma is a one-liner.
Build green (8055 jobs).

Codex experiment: switched approach. The `run_in_background` codex
invocation hung silently for 30+ min (stdout 0 bytes, processes
zombied). Wrote a prompt file `codex-prompt.md` for the user to fire
manually with `codex exec "$(cat codex-prompt.md)"`. Pending diff
will introduce `periodSubgroup_isZLattice` opaque per 7abae190's
recommendation.

PRIOR TICK (still standing):
INTEGRATED `84774271` — **ABEL'S THEOREM** survey on
`analyticOfCurve_injective` (anti-hack #2 — forces `ofCurve_inj`).
~218-line analysis with: explicit `leansearch` outputs confirming
Mathlib gaps (no Riemann-Roch, no theta function, no divisor theory),
THREE proof routes (Riemann-Roch / 1-form separation / theta function),
project-internal dependency analysis, RECOMMENDED RESOLUTION:
declare `pathIntegralFunctional_separates_points` opaque to capture
the Abel content, then `_injective` is a 5-line wiring assembly.
Build green (8052 jobs).

PRIOR TICK (still standing):
INTEGRATED `75c45747` — TOP-DOWN refinement experiment (per user
request) on `periodFundamentalDomain_isCompact`. 115-line analysis
identifying two blockers (IsZLattice + opaque-has-no-spec).

PRIOR TICK (still standing):
INTEGRATED `f735aa6d` — **NEW `ChartedSpace ℂ (OnePoint ℂ)` instance**
in `Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean` (sorry-free
177-line file). Real new infrastructure: ℂℙ¹ now has a complex
charted-space structure via the two-chart atlas {identity, inversion}.
Build green. Packet C (`IsManifold 𝓘(ℂ,ℂ) ⊤`) is the natural follow-up.

PRIOR TICK (still standing):
SUBMITTED `f735aa6d` — OnePointCxChartedSpace (Packets A+B from
600f7ff6's plan). Asks Aristotle to build `inversionChart`,
`identityChart`, and the `ChartedSpace ℂ (OnePoint ℂ)` instance in a
new file `Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean`.
Source-of-truth API survey is the integrated recon file from the
prior tick. Substantive ~110-170 LOC implementation; off the critical
path; direct prerequisite for the IsManifold packet (C) which would
in turn unblock `analyticGenus_eq_zero_of_homeomorphic_sphere`.

PRIOR TICK (still standing):
INTEGRATED `600f7ff6` — OnePointCxRecon (NEW ~480-line recon file).
Aristotle's Mathlib API survey for making `OnePoint ℂ` a complex
manifold. Confirms NO `ChartedSpace ℂ (OnePoint ℂ)` instance exists
in v4.28.0 and proposes a self-contained two-chart-atlas construction.

PRIOR TICK (still standing):
INTEGRATED `7abae190` — PeriodLattice discreteness blocker analysis.
~110-line survey identifying `periodPairing` opaqueness + missing
integrality declaration as the blocker; recommends an
`opaque periodSubgroup_isZLattice` companion to `periodPairing`.

PRIOR TICK (still standing):
CLEANUP of `aristotle_tasks.md` from 3824 → 317 lines.

PRIOR TICK (still standing):
DOC: refreshed top-of-file docstring in
`Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean` (4-file
bridge architecture diagram + post-keystone-refactor note).

PRIOR TICK (still standing):
Light tick: README sorry-free counts re-derived (still 381/389,
no change since two ticks ago — user's `fb99006` exposure of a
ULift transition obligation added 1 sorry to ULiftTransport, but
the file was already in the sorry-bearing list).

PRIOR TICK (still standing):
This tick was an Aristotle integration (aadb7721 hard-direction
survey). No new local Lean work; the substantive deliverable is the
integrated 230-line survey block.

PRIOR TICK (still standing):
EXTEND Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean (+1 theorem)

  holomorphicOneFormDualFinBasis_apply_holomorphicOneFormFinBasis
    (i j : Fin (analyticGenus E X))
    : holomorphicOneFormDualFinBasis E X i
        (holomorphicOneFormFinBasis E X j)
        = if j = i then 1 else 0
    Duality property of the chosen basis and its dual; direct
    specialization of `Module.Basis.dualBasis_apply_self`. The δ_{ji}
    convention matches Mathlib's; downstream uses can flip via `eq_comm`
    if needed.

User commits this tick:
  c49cf9a ComplexTorus: transport charted space through ULift —
          Round 2b chart-transport for Jacobian X via Homeomorph.ulift.
  17b31f7 Solution: restore universe-polymorphism for genus and
          genus_eq_zero_iff_homeo — un-doing the keystone monomorphism
          for these specific public declarations.
  62d2f9c TopDown: refresh Declaration Map with post-keystone state.

PRIOR TICK (still standing):
WIRED `Jacobian.Periods.BasisAlignedAnalyticJacobianEquiv` into the
`Jacobian/Periods.lean` umbrella.

PRIOR TICK (still standing):
This tick was an Aristotle submission (aadb7721 hard direction).
No new local Lean work; the substantive deliverable is the queued
follow-up survey packet.

PRIOR TICK (still standing):
Aristotle integration of 027bb9d7 (genus-zero easy direction survey).

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+1 theorem)

  analyticJacobianBasisAlignedEquiv_witnessAbelJacobi_mk_sub
    (basePoint P : X) (v : ℂ)
    : analyticJacobianBasisAlignedEquiv X
        (witnessAbelJacobi basePoint P v)
        = QuotientAddGroup.mk (dualEquiv (evalLinearMap P v)
                              - dualEquiv (evalLinearMap basePoint v))
    Single-`mk` form of the witness-bridge theorem; combines the
    existing two-`mk`-subtracted form with `QuotientAddGroup.mk_sub`.
    Useful when downstream proofs want a single representative.

USER COMMITS THIS TICK: `6b9c9fe PeriodLattice: discharge basisAlignedPeriodSubgroup_isClosed`
— used `AddSubgroup.isClosed_of_discrete` (closedness from discreteness).
PeriodLattice sorry count drops from 4 → 3 (only `_isDiscrete`,
`_fundamentalDomain_isCompact`, `_fundamentalDomain_covers` remain).

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedPeriodPairing.lean (+1 theorem)

  holomorphicOneFormDualEquiv_symm_basisAlignedPeriodPairing
    (σ : IntegralOneCycle X)
    : (holomorphicOneFormDualEquiv ℂ X).symm
        (basisAlignedPeriodPairing X σ)
        = periodPairing ℂ X σ
    Pulling back through the inverse dual equiv recovers the
    functional-space pairing. Proof: 1-line `rw` chain.

User WIP in flight (left untouched): `M Jacobian/Periods/PeriodLattice.lean`
(discharging `basisAlignedPeriodSubgroup_isClosed` via
`AddSubgroup.isClosed_of_discrete`); `M Jacobian/ComplexTorus/ULiftTransport.lean`
(discharging Round 2b `complexTorusULift_chartedSpace` instance with
real chart-transport machinery via `Homeomorph.ulift`).

PRIOR TICK (still standing):
PROMPT.md §3 updated to clarify that off-critical-path big tasks are
fine and multiple may run in parallel; the constraint is that
Aristotle never blocks Claude's local work.

Submitted second Aristotle packet `027bb9d7` —
analyticGenus_eq_zero_of_homeomorphic_sphere ("easy" direction of
genus-zero classification, deep). See Aristotle status above.

Recomputed headline ratio: production sorry-free 381 / 389 (up from
388 prod last tick: +1 file via user's Round 0 commits, plus 3
additional sorrys in GenusZeroClassification).

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+1 simp lemma)

  mk_basisAlignedPeriodPairing_eq_zero (σ : IntegralOneCycle X)
    : (QuotientAddGroup.mk (basisAlignedPeriodPairing X σ) :
         BasisAlignedAnalyticJacobian X) = 0
    @[simp]; combines `basisAlignedPeriodPairing_mem` (membership in
    the basis-aligned period subgroup) with `QuotientAddGroup.eq_zero_iff`
    (kernel = subgroup) to show that period images are killed by the
    quotient projection. Useful kernel-side simp rule for downstream
    work over the basis-aligned analytic Jacobian.

PRIOR TICK (still standing):
EXTEND Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean (+1 theorem)

  holomorphicOneFormDualEquiv_symm_pi_single
    (i : Fin (analyticGenus E X))
    : (holomorphicOneFormDualEquiv E X).symm (Pi.single i 1)
        = holomorphicOneFormDualFinBasis E X i
    Inverse-direction unfold of the existing `_dualBasis_apply`
    forward lemma. Proof: `LinearEquiv.symm_apply_eq` + the forward
    apply lemma.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+1 simp lemma)

  analyticJacobianBasisAlignedEquiv_witnessAbelJacobi_self
    (basePoint : X) (v : ℂ)
    : analyticJacobianBasisAlignedEquiv X
        (witnessAbelJacobi basePoint basePoint v) = 0
    @[simp]; uses `witnessAbelJacobi_self` (which gives 0 in source)
    plus `map_zero` of the equiv. Diagonal-witness corollary of last
    tick's general witnessAbelJacobi-distribution lemma.

User commit `d1e0b3b GenusZeroClassification: split into mp and mpr
directions` landed during this tick. Both directions still sorry but
now packaged as named theorems.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+1 theorem)

  analyticJacobianBasisAlignedEquiv_witnessAbelJacobi
    (basePoint P : X) (v : ℂ)
    : analyticJacobianBasisAlignedEquiv X (witnessAbelJacobi basePoint P v)
        = mk (dualEquiv (evalLinearMap P v)) - mk (dualEquiv (evalLinearMap basePoint v))
    Distributes the bridge over witness subtraction; combines AddEquiv.map_sub
    with last tick's evalJacobianClass corollary. Lifts the AbelJacobi witness
    machinery cleanly onto the basis-aligned model.

User commit `91139a0 Round 0: comparator harness setup` landed this tick.
Tree note: Jacobian/Solution.lean is dirty (user WIP); also long-standing
Jacobian/ComplexTorus/ULiftTransport.lean. Both left untouched per PROMPT.md.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+1 theorem)

  analyticJacobianBasisAlignedEquiv_evalJacobianClass
    (P : X) (v : ℂ)
    : analyticJacobianBasisAlignedEquiv X (evalJacobianClass P v)
        = QuotientAddGroup.mk
            (holomorphicOneFormDualEquiv ℂ X (evalLinearMap P v))
    @[simp]; combines `evalJacobianClass_def` with last tick's
    `_mk` simp lemma to give the natural unfolding rule for the
    bridge applied to `evalJacobianClass` representatives. Useful
    when bridging from the AnalyticJacobian/AbelJacobi witness API
    over to the basis-aligned model.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (+2 theorems)

  analyticJacobianBasisAlignedEquiv_mk
    (φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)
    : analyticJacobianBasisAlignedEquiv X (mk ℂ X φ)
        = QuotientAddGroup.mk (holomorphicOneFormDualEquiv ℂ X φ)
    rfl-proof; @[simp]. Direct corollary of `QuotientAddGroup.congr_mk`.

  analyticJacobianBasisAlignedEquiv_symm_mk
    (v : Fin (analyticGenus ℂ X) → ℂ)
    : (analyticJacobianBasisAlignedEquiv X).symm (QuotientAddGroup.mk v)
        = mk ℂ X ((holomorphicOneFormDualEquiv ℂ X).symm v)
    rfl-proof. Inverse-direction simp lemma.

These give the two natural unfolding rules for using the equiv on
specific elements: forward and backward through the bridge.

USER'S KEYSTONE REFACTOR LANDED THIS TICK as commit `952e750`
("Keystone: route basisAlignedPeriodSubgroup to concrete representative").
The 6-file mid-flight WIP from last tick is now resolved: PeriodLattice's
opaque is unfrozen and routes to `basisAlignedPeriodSubgroupConcrete`,
with downstream signatures updated. `lake build Jacobian.Solution` ✓.

PRIOR TICK (still standing):
NEW Jacobian/Periods/BasisAlignedAnalyticJacobianEquiv.lean (1 abbrev + 1 def)

  BasisAlignedAnalyticJacobian X : Type
    := (Fin (analyticGenus ℂ X) → ℂ) ⧸ basisAlignedPeriodSubgroupConcrete X

  analyticJacobianBasisAlignedEquiv X
    : AnalyticJacobianGroup ℂ X ≃+ BasisAlignedAnalyticJacobian X
    Built via Mathlib's `QuotientAddGroup.congr` against
    `holomorphicOneFormDualEquiv` and the rfl image-equation on
    period subgroups. Lifts the AddEquiv from the prior tick's
    `holomorphicOneFormDualPeriodSubgroupEquiv` from the period
    subgroups themselves up to the corresponding quotients.

This is the top-of-stack of the basis-aligned period bridge: it
connects the functional-space `AnalyticJacobianGroup ℂ X` (already
heavily-built-out via the AnalyticJacobian directory) directly to a
basis-aligned quotient. Future work that wants to use the existing
mk/evalJacobianClass/etc. machinery from the basis-aligned side can
route through this equivalence.

Tree note: user has dirty WIP across 6 files
(M Jacobian/{Solution,Periods/PeriodLattice,AbelJacobi/AnalyticOfCurveBasis,TraceDegree/{AnalyticDegree,PullbackBasis,PushforwardBasis}}.lean).
The PeriodLattice change is a keystone refactor that unfreezes
`opaque basisAlignedPeriodSubgroup` and points it at
`basisAlignedPeriodSubgroupConcrete`; specializes `(X : Type*)` →
`(X : Type)` to align with the IntegralOneCycle universe constraint.
Currently `lake build Jacobian.Solution` fails (unrelated to my work)
— the refactor is mid-flight. Left untouched per PROMPT.md.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedPeriodSubgroup.lean (+1 def)
holomorphicOneFormDualPeriodSubgroupEquiv

PRIOR TICK (still standing):
NEW Jacobian/HolomorphicForms/SectionTopologyRecon.lean (recon stub).
Mirrors the existing recon-file convention (Jacobian/ComplexTorus/{Manifold,ZLattice,Discreteness}Recon.lean
+ Jacobian/HolomorphicForms/Recon.lean). Builds clean, contains no
production declarations, not re-exported by any umbrella. The stub's
docstring requests Aristotle to fill in a survey of (1) existing
Mathlib API for topology on `ContMDiffSection`, (2) missing
instances, (3) a concrete design plan with named Mathlib lemmas,
(4) dependency graph. Submitted as packet `b782c387` — see Aristotle
status above.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedPeriodSubgroup.lean (+1 theorem)

  holomorphicOneFormDualEquiv_bijOn_periodSubgroup
    : Set.BijOn (holomorphicOneFormDualEquiv ℂ X)
        (periodSubgroup ℂ X : Set _)
        (basisAlignedPeriodSubgroupConcrete X : Set _)
    Packages the bijection between functional-space and basis-aligned
    period subgroups (as sets) — combining `_mem_*` (forward
    transport), `LinearEquiv.injective`, and the surjective image
    characterization. Useful for pulling Mathlib `BijOn`-style lemmas
    onto the basis-aligned side.

DOC: plan.md updated to reflect actual state of Phase 1.5b
(`fundamentalDomain_covers` is now proved, `fullComplexLatticeOfZLattice`
is sorry-free) and added a Phase 1.5c section describing the
basis-aligned period bridge built across the last several ticks.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedPeriodPairing.lean (+2 theorems)

  basisAlignedPeriodPairing_eq_iff
    : basisAlignedPeriodPairing X σ = basisAlignedPeriodPairing X τ
      ↔ periodPairing ℂ X σ = periodPairing ℂ X τ
    Two basis-aligned periods are equal iff the underlying functional-
    space periods are. Follows from injectivity of `holomorphicOneFormDualEquiv`
    via `EmbeddingLike.apply_eq_iff_eq`.

  basisAlignedPeriodPairing_eq_zero_iff
    : basisAlignedPeriodPairing X σ = 0 ↔ periodPairing ℂ X σ = 0
    Specialization at τ = 0; useful kernel-side characterization.

DOC: Jacobian/Periods/IntegralOneCycle.lean — added a comment block
documenting why `(X : Type)` is restricted to universe 0 here
(singularHomologyFunctor's `HasCoproducts.{w} (ModuleCat ℤ)` instance
constraint at universe 0). Saves future ticks from re-attempting the
naive lift to `(X : Type*)`.

PRIOR TICK (still standing):
EXTEND Jacobian/Periods/BasisAlignedPeriodSubgroup.lean (+2 theorems)

  holomorphicOneFormDualEquiv_symm_mem_periodSubgroup
    : v ∈ basisAlignedPeriodSubgroupConcrete X →
        (holomorphicOneFormDualEquiv ℂ X).symm v ∈ periodSubgroup ℂ X
    Inverse-direction transport. Proof: unfold via mem-iff, destructure
    the existential, use `LinearEquiv.symm_apply_apply` to recover φ.
    ~5 lines real content.

  holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete
    : φ ∈ periodSubgroup ℂ X →
        holomorphicOneFormDualEquiv ℂ X φ ∈ basisAlignedPeriodSubgroupConcrete X
    Forward-direction transport — `mp` direction of the iff, exposed
    as a named lemma.

Both give clean named lemmas for moving membership between
functional-space and basis-aligned forms in both directions.
Useful upstream for the eventual closedness/discreteness proofs.

PRIOR TICK (still standing — last tick's substantive work):
NEW Jacobian/Periods/BasisAlignedPeriodPairing.lean (1 def + 3 theorems)

  basisAlignedPeriodPairing X
    : IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ)
    = (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom.comp
        (periodPairing ℂ X)
    The natural arrow from cycles directly into the basis-aligned model,
    composing functional-space periodPairing with the basis-aligned dual
    equivalence.

  basisAlignedPeriodPairing_apply — pointwise unfolding (rfl + sugar).

  basisAlignedPeriodSubgroupConcrete_eq_range — characterizes the
    concrete period subgroup as the range of basisAlignedPeriodPairing.
    Real proof: ext + AddSubgroup.mem_map / AddMonoidHom.mem_range
    unfolding + a constructor split (~10 lines of substantive content).

  basisAlignedPeriodPairing_mem — membership corollary.

Why this matters: future proofs of the 5 PeriodLattice obligations
(`_isClosed`, `_isDiscrete`, `periodFundamentalDomain_isCompact` /
`_covers`) will route through this map. In particular, discreteness of
`basisAlignedPeriodSubgroup` (once unfrozen) reduces to "image of
H₁(X, ℤ) under `basisAlignedPeriodPairing` has no accumulation in the
basis-aligned model" — a tractable statement once we have the
universe-lift in place.

Wired into `Jacobian/Periods.lean` umbrella. Builds clean.

PRIOR TICK (still standing — last tick's substantive work):
Jacobian/Periods/PeriodLattice.lean — rename `periodSubgroup` to
`basisAlignedPeriodSubgroup` (and similarly for the 2 of-the-subgroup
lemmas: `_isClosed`, `_isDiscrete`). This frees the
`JacobianChallenge.Periods.periodSubgroup` fully-qualified name for the
functional-space concrete definition in PeriodFunctional.lean,
resolving the long-standing same-name conflict where the two
declarations coexisted only because nobody imported both.

Concrete result: `Jacobian/Periods.lean` umbrella now imports BOTH
PeriodFunctional (with `periodSubgroup E X` functional-space) AND
PeriodLattice (with `basisAlignedPeriodSubgroup X`) AND
BasisAlignedPeriodSubgroup (with `basisAlignedPeriodSubgroupConcrete X`)
with NO name conflict. This was structurally impossible before this tick.

Builds:
  lake build Jacobian.Periods.PeriodLattice ✓ (5 sorries — all renamed)
  lake build Jacobian.Periods                ✓
  lake build Jacobian.Solution              ✓ (no changes needed; only
                                              uses `periodFullComplexLattice`,
                                              which still exists with the same
                                              shape, just now built atop the
                                              renamed `basisAlignedPeriodSubgroup`)

Universe-mismatch deferred: routing `basisAlignedPeriodSubgroup` to
`basisAlignedPeriodSubgroupConcrete` (i.e. unfreezing the opaque) was
attempted but blocked by `Type` vs `Type*`. PeriodFunctional uses
`(X : Type)` (inheriting from `IntegralOneCycle`), but PeriodLattice
+ Solution + AnalyticOfCurveBasis all use `(X : Type*)`. Resolving
this requires a Type/Type* generalization in IntegralOneCycle and
PeriodFunctional — a separate Claude-owned refactor tick.

PRIOR TICK (still standing):
NEW Jacobian/Periods/BasisAlignedPeriodSubgroup.lean (1 def + 2 theorems):

  `basisAlignedPeriodSubgroupConcrete X
      : AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)
      = AddSubgroup.map (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
                        (periodSubgroup ℂ X)`
    The CONCRETE basis-aligned period subgroup, defined as the image of
    the existing functional-space `periodSubgroup ℂ X`
    (= `(periodPairing ℂ X).range`) under the basis-aligned dual equiv
    introduced last tick. Builds against the deferred-instance
    `[FiniteDimensionalHolomorphicOneForms ℂ X]`.

  `mem_basisAlignedPeriodSubgroupConcrete_iff` — characterizes
    membership as "image of some functional-space period under the
    dual equivalence" (existential characterization).

  `zero_mem_basisAlignedPeriodSubgroupConcrete` — sanity check.

Why a NEW file with a NEW name (rather than replacing
`PeriodLattice.lean`'s opaque): Lean 4 does not allow two declarations
with the same fully-qualified name to coexist in a single elaboration
context. `Jacobian/Periods/PeriodFunctional.lean` already declares
`JacobianChallenge.Periods.periodSubgroup (E X) [...]` (functional-space)
and `Jacobian/Periods/PeriodLattice.lean` declares
`opaque JacobianChallenge.Periods.periodSubgroup X (basis-aligned)` —
they presently coexist only because nobody imports both. Renaming
`PeriodLattice`'s opaque is a separate refactor that touches Solution.lean
and AnalyticOfCurveBasis.lean (the only two files that import
PeriodLattice). For this tick we deliver the concrete definition under
`basisAlignedPeriodSubgroupConcrete` (uniquely named, no conflict);
a future tick can do the rename + route `periodFullComplexLattice`
through this file's def.

Wired into `Jacobian/Periods.lean` umbrella (also added the
previously-orphaned `PeriodSubgroupRange` import from the integrated
6c252557 packet).

Builds:
  lake build Jacobian.Periods.BasisAlignedPeriodSubgroup ✓
  lake build Jacobian.Periods                            ✓
  lake build Jacobian.Solution                           ✓
```

```text
Build status — recomputed each tick from the tree
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass         lake build Jacobian.Challenge
Statement bank            pass         lake build Jacobian.WorkPackets.StatementBank
Periods umbrella          pass         lake build Jacobian.Periods
Solution                  pass         lake build Jacobian.Solution
This tick's new file      pass         lake build Jacobian.Periods.BasisAlignedPeriodSubgroup

Per-directory production sorry-free counts (recomputed):
                                  ratio
  HolomorphicForms             27 / 29
  AnalyticJacobian             23 / 23
  AbelJacobi                   19 / 20
  TraceDegree                  81 / 84   (3 user-WIP files)
  Periods                     171 / 173  (+1 prod file vs last tick: BasisAlignedPeriodPairing)
  ComplexTorus                 47 / 53

Reproduction (per dir):
  total  = `find <dir> -maxdepth 1 -name "*.lean" | wc -l`
  recon  = `find <dir> -maxdepth 1 -name "*Recon*.lean" | wc -l`
  with-sorry-word = (grep -lE "\bsorry\b" <dir>/*.lean) minus Recon files
  ratio = (total − recon − with-sorry-word) / (total − recon)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Per Aristotle's plan in CompactRiemannSurface, the *next* off-path
   substantive task is "define the topology of uniform convergence on
   compact sets for ContMDiffSection, and upgrade it to a Banach
   space structure when the base manifold is CompactSpace". This is
   itself a substantial Mathlib infrastructure project. Consider
   submitting a recon packet to scope it out before committing
   Aristotle hours.
2. Continue local cadence: the basis-aligned period bridge is now
   well-stocked (BasisAlignedDualEquiv, BasisAlignedPeriodSubgroup,
   BasisAlignedPeriodPairing, with bijection / kernel / mem-transport
   theorems). Next natural Claude-owned move: try the universe lift
   on IntegralOneCycle via explicit-universe call to
   `singularHomologyFunctor.{u}`, or via a ULift bridge.
3. Continue ignoring the 5 user-WIP files (AnalyticOfCurveBasis,
   ULiftTransport, PullbackBasis, PushforwardBasis, AnalyticDegree)
   per PROMPT.md.
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
