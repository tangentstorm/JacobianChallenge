# Aristotle Task Index

This file indexes the Lean statement bank in
`Jacobian/WorkPackets/StatementBank.lean`.

Claude should treat each queue below as a source of small Aristotle jobs. Before
submitting, Claude should copy the relevant declarations into a narrower target
file and ask Aristotle to work only on that file.

The Aristotle account is shared with other projects; job IDs from
`aristotle list` may belong to FourColor or other unrelated work. Record every
JacobianChallenge submission in `aristotle_jobs.jsonl` so future ticks can
identify our jobs without inspecting tarballs.

## Live Status (2026-04-26 12:19 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralViaChartAdd.lean`:
    `pathIntegralViaChart_add_of_curveIntegrable` — 2-line `unfold;
    exact` delegating through the in-chart version landed last tick.
  - NEW `Jacobian/Periods/PathIntegralViaChartSub.lean`:
    `pathIntegralViaChart_sub_of_curveIntegrable` — same shape.
  - Both wired into `Jacobian/Periods.lean` umbrella; builds green
    (2676 jobs, 24s each).
- Provisional from-X linearity ladder is now complete and parallel
  to the corrected from-X layer.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:15 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormSub.lean`: `chartedForm_sub`
    (provisional layer) — 1-line `rw [sub_eq_add_neg, sub_eq_add_neg,
    chartedForm_add, chartedForm_neg]`.
  - NEW `Jacobian/Periods/PathIntegralChartAdd.lean`:
    `pathIntegralInChart_add_of_curveIntegrable` — conditional
    addition linearity at the provisional in-chart layer
    (`curveIntegral_add` needs CurveIntegrable). Mirrors corrected.
  - NEW `Jacobian/Periods/PathIntegralChartSub.lean`:
    `pathIntegralInChart_sub_of_curveIntegrable` — same shape.
  - All three wired into `Jacobian/Periods.lean` umbrella; builds
    green (2672 jobs, 21-22s each).
- Provisional in-chart linearity ladder is now complete to match
  the corrected layer:
  zero ✓, neg ✓, smul ✓, refl ✓, symm ✓, add (cond) ✓, sub (cond) ✓.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:10 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralChartLinear.lean`:
    `pathIntegralInChart_neg` and `pathIntegralInChart_smul` at
    the provisional in-chart layer (the `_zero` already lives in
    `PathIntegralChart.lean`). Three-line proofs each: `show ...
    rw [chartedForm_neg, curveIntegral_neg]` and the smul analogue.
    Mirror of `PathIntegralChartCorrect{Linear,Smul}` at the
    corrected layer.
  - Refactored `Jacobian/Periods/PathIntegralViaChartLinear.lean`
    (the from-X version landed at 11:38) to delegate through the
    new in-chart lemmas: `unfold pathIntegralViaChart; exact
    pathIntegralInChart_{neg,smul} c ω _` (2 lines per lemma,
    down from 3). Cleaner because the chartLift application is now
    just an underscore.
  - Build green: `lake build Jacobian.Periods.PathIntegralChartLinear`
    → 2672/2672 (58s); refactored ViaChart version → 2674/2674 (51s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:05 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - Refactored `pathIntegralViaChartCorrect_symm` (in
    `PathIntegralViaChartCorrect.lean`) and `pathIntegralViaChart_symm`
    (in `PathLiftSimp.lean`) to use the new `chartLift_symm` lemma
    landed last tick. Each proof shrinks from a 5-line inline
    `Path.ext rfl` setup to a 3-line `unfold; rw; exact` chain.
  - Build green: `lake build Jacobian.Periods.PathIntegralViaChartCorrect`
    → 2675/2675 (47s); `Jacobian.Periods.PathLiftSimp` →
    2672/2672 (54s).
- Cumulative session: 7 new local helpers/refactors today
  (4 toolkit lemmas + 3 proof-cleanup refactors), total
  net negative line count vs the original inline proofs.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:02 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartLiftSymm.lean` — new file with
    `chartLift_symm : chartLift c γ.symm h' = (chartLift c γ h).symm`.
    Proof is `unfold chartLift; exact Path.ext rfl` — both sides
    expand to `c ∘ γ ∘ σ`, the σ just gets factored out at
    different points in the bracketing. Promotes the inline
    `Path.ext rfl` from `pathIntegralViaChartCorrect_symm`
    (PathLiftSimp.lean) to a reusable named lemma.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2671 jobs, 51s).
- This is the fourth helper toward `pathIntegralViaCoverWith_symm`.
  Status of toolkit:
  1. `divFinIcc_symm` ✓ (boundary point reflection)
  2. `path_symm_subpath_eq` ✓ (subpath through symm)
  3. `path_symm_subpath_divFinIcc` ✓ (segment-level reflection)
  4. `chartLift_symm` ✓ (chartLift commutes with symm) — NEW
  Still needed: Fin.rev re-indexing of the Finset sum (the easy
  combinatorial step).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:58 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathPartitionSymm.lean` — new file with
    `path_symm_subpath_divFinIcc`:
    ```
    γ.symm.subpath (i/n) ((i+1)/n)
      = (γ.subpath (σ ((i+1)/n)) (σ (i/n))).symm
    ```
    First attempt expanded σ via `divFinIcc_symm` inside the type
    and hit a type mismatch (Path endpoints involve `γ.symm s` vs
    `γ ((n-i)/n)`, which are equal propositionally via
    `divFinIcc_symm` but not definitionally). Fixed by keeping σ
    in the statement so endpoints unify via `γ.symm s = γ (σ s)`
    (which IS rfl). Proof reduces to a 2-line rw chain.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (`lake build Jacobian.Periods.PathPartitionSymm` →
    1582 jobs, 31s).
- This is the third helper toward `pathIntegralViaCoverWith_symm`,
  combining the previous `divFinIcc_symm` and `path_symm_subpath_eq`
  into one usable segment-level identity.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:53 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathSymmSubpath.lean` — new file with
    `path_symm_subpath_eq : γ.symm.subpath s t = γ.subpath (σ s) (σ t)`.
    Proof: `Path.ext + funext + show + congr + Subtype.ext + ring`,
    discharging the underlying real identity
    `1 - ((1-r)s + rt) = (1-r)(1-s) + r(1-t)`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (`lake build Jacobian.Periods.PathSymmSubpath` → 1580 jobs, 45s).
- This is the second prerequisite helper for the eventual
  `pathIntegralViaCoverWith_symm` proof, after `divFinIcc_symm`
  (last tick): with both lemmas in hand, the partition-by-partition
  re-indexing for γ.symm reduces to `Fin.rev` re-indexing of the
  Finset sum.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:49 EDT)

- Active jobs (ours): 0/5 (queue empty; 3 cancelled today during
  the ~7.5h backend freeze).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/DivFinIcc.lean`: added `divFinIcc_symm`
    (`σ (divFinIcc n hn i hi) = divFinIcc n hn (n - i) ...`),
    the partition-point reflection identity. Proof in 4 lines:
    `apply Subtype.ext; show 1 - (i:ℝ)/n = ((n-i:ℕ):ℝ)/n;
    rw [Nat.cast_sub hi, sub_div, div_self _]`. This is a
    prerequisite helper for `pathIntegralViaCoverWith_symm`
    (the partition reflects under `γ.symm`, so segment `i` of
    `γ.symm` lives at `[σ((i+1)/n), σ(i/n)] = [(n-i-1)/n, (n-i)/n]`).
  - Build green (`lake build Jacobian.Periods.DivFinIcc` →
    1361 jobs, 32s).
- **Submitted this tick:** none.
- Continuing to set up substantive Claude-owned proof work
  toward `pathIntegralViaCoverWith_symm` while backend frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:45 EDT)

- Active jobs (ours): 0/5 (queue empty; 3 cancelled today during
  the ~7.5h backend freeze).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - Refactored `pathIntegralInChartCorrect_neg` (in
    `PathIntegralChartCorrectLinear.lean`) from a 22-line proof
    to a 7-line proof: replaced inline `funext +
    ContinuousLinearMap.neg_comp` chain with `rw
    [chartedFormPullback_neg, curveIntegral_neg]` using the modern
    simp lemma I added at 10:39.
  - Same refactor for `pathIntegralInChartCorrect_smul` in
    `PathIntegralChartCorrectSmul.lean` (from 20 lines to 7).
  - Net change: -29 lines of dead boilerplate; same theorem
    signatures and statements. Build green
    (`lake build Periods.PathIntegralChartCorrectLinear
    Periods.PathIntegralChartCorrectSmul` → 2673 jobs, 61s).
- **Submitted this tick:** none.
- Queue is empty. Next: pick up substantive Claude-owned work
  (e.g. `pathIntegralViaCoverWith_symm`, well-definedness of
  `pathIntegralViaCover`, or decomposed TorusExample retry).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:42 EDT)

- Active jobs (ours): 0/5. **In-flight queue fully drained
  locally** during the ~7.5h backend freeze (3 cancelled jobs
  today: f8faacda, bf7d62c4, 82687eb7 — all proved in-house).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunSimpApply.lean` — three
    pointwise apply-form simp lemmas
    `pullbackFormsFun_{zero,neg,smul}_apply`. Proved by
    `rw [pullbackFormsFun_{zero,neg,smul}]; rfl` (2 lines each).
  - **In-flight job `82687eb7` cancelled** after local landing.
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2410 jobs, 50s).
- **Submitted this tick:** none.
- Queue is now empty. Next ticks need to either (a) wait for backend
  recovery, (b) prepare and submit a new substantive packet, or
  (c) continue local Claude-owned proof work on bigger items
  (e.g. pathIntegralViaCoverWith_symm, well-definedness of
  pathIntegralViaCover, decomposed TorusExample retry).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:38 EDT)

- Active jobs (ours): 1/5. One QUEUED ~7.5h
  (`82687eb7` PullbackFunSimpApply) — backend stalled since
  ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathIntegralViaChartLinear.lean` —
    `pathIntegralViaChart_neg` and `pathIntegralViaChart_smul` for
    the provisional from-X integral. Proof per lemma:
    `show curveIntegral (chartedForm c _) (chartLift c γ h) = ...; rw [chartedForm_neg/smul, curveIntegral_neg/smul]`
    (3 lines).
  - **In-flight job `bf7d62c4` cancelled** after local landing
    (was QUEUED ~7.5h with no progress).
  - Wired into `Jacobian/Periods.lean` umbrella; module builds
    green (2673 jobs, 55s).
- **Submitted this tick:** none.
- Continuing to drain in-flight queue locally while backend frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:34 EDT)

- Active jobs (ours): 2/5. Two QUEUED ~7.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartLiftBoundary.lean` — `chartLift_zero`
    and `chartLift_one` boundary-value simp lemmas. Proved by
    `rw [chartLift_apply, γ.source]` and `rw [chartLift_apply, γ.target]`
    respectively (2 lines each).
  - **In-flight job `f8faacda` cancelled** after local landing
    (was QUEUED ~7.5h with no progress).
  - Wired into `Jacobian/Periods.lean` umbrella; module builds
    green (2672 jobs, 38s).
- **Submitted this tick:** none.
- Per user feedback: when backend is frozen, do substantive local
  proof work each tick instead of refresh-only commits.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:33 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over ~25 min
  across 4 new files. Trivial-apply category exhausted; further
  work needs substantive lemmas best delegated to Aristotle once
  backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:06 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over ~25 min
  across 4 new files. Trivial-apply category exhausted; further
  work needs substantive lemmas best delegated to Aristotle once
  backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:03 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.9h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over the last
  ~25 minutes across 4 new files. Trivial-apply category
  exhausted; further work needs substantive lemmas best delegated
  to Aristotle once backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:00 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.8h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear); this is a 1-minute-after
  refresh tick.
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over the last
  ~25 minutes (ChartedFormPullbackApplyLinear,
  ChartedFormPullbackLinearMapApplyLinear, PullbackFunAddSubApply,
  PullbackFormsLinearMapApplyLinear). Trivial-apply category
  exhausted; further work would need substantive lemmas best
  delegated to Aristotle once backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:59 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.8h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:54 just landed five LinearMap-layer apply-form lemmas in
  `PullbackFormsLinearMapApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:54 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFormsLinearMapApplyLinear.lean` —
    five pointwise apply-form simp lemmas at the bundled-LinearMap
    layer: `pullbackFormsLinearMap_{zero,neg,add,sub,smul}_apply`.
    Each rewrites the function-level simp and closes by `rfl`.
    Mirrors the Periods-side
    `ChartedFormPullbackLinearMapApplyLinear` landed at 10:43.
    Out of scope of any in-flight Aristotle job.
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2416 jobs, 99s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:51 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:48 just landed `pullbackFormsFun_{add,sub}_apply` in
  `PullbackFunAddSubApply`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:48 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunAddSubApply.lean` — two
    pointwise apply-form simp lemmas:
    `pullbackFormsFun_add_apply` and `pullbackFormsFun_sub_apply`.
    Each rewrites the function-level simp and closes by `rfl`.
    Out of scope of the in-flight Aristotle job 82687eb7
    (`PullbackFunSimpApply.lean`, which targets only
    `_zero/_neg/_smul_apply`).
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2410 jobs, 25s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:46 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:43 just landed 5 LinearMap-layer apply-form lemmas in
  `ChartedFormPullbackLinearMapApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick — wakeup fired sooner than the
  scheduled 30 min window. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:43 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartedFormPullbackLinearMapApplyLinear.lean` —
    five pointwise apply-form simp lemmas at the bundled-LinearMap
    layer: `chartedFormPullbackLinearMap_{zero,neg,add,sub,smul}_apply`.
    Each delegates through `chartedFormPullbackLinearMap_apply_at`
    (the rfl-bridge to the unbundled form) to the apply-form bundle
    landed in the previous tick.
  - Wired into `Jacobian/Periods.lean` umbrella; module builds green
    (2418 jobs, 35s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:41 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:39 just landed 5 pointwise apply-form simp lemmas in
  `ChartedFormPullbackApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick — wakeup fired sooner than
  expected. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:39 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartedFormPullbackApplyLinear.lean` — five
    pointwise apply-form simp lemmas:
    `chartedFormPullback_{zero,neg,add,sub,smul}_apply`. Each
    rewrites the function-level simp lemma and closes by `rfl`.
    Useful for direct-tactic proofs (Aristotle prompt style)
    without invoking the full simp set.
  - Wired into `Jacobian/Periods.lean` umbrella; Periods builds
    green (8083/8083, 162s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:27 EDT)

- Active jobs (ours): 3/5. All three QUEUED 2h+ — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none.
- **Submitted this tick:** none (backlog still blocking).
- Bookkeeping tick. Waiting on backend recovery.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 05:17 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~1 hr — backend
  stalled since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFormsLinearMapSimp.lean`:
    +`pullbackFormsLinearMap_sub` (LinearMap-derived subtraction
    linearity, named simp lemma matching the existing
    `_zero`/`_neg`/`_add` pattern).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 05:16 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~57 min — backend
  stalled since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunApplyVec.lean` — tangent-vector
    apply: `(pullbackFormsFun f η x) v = η.toFun (f x) (mfderiv f x v)`,
    a `rfl` chain-rule unfolding.
  - `Jacobian/TraceDegree/PullbackFunSub.lean` — subtraction
    linearity: `pullbackFormsFun_sub` derived from `_add`/`_neg`.
  - Both wired into `Jacobian/TraceDegree.lean` umbrella.
- **Submitted this tick:** none (backlog still blocking).
- No-op-on-Aristotle, locally productive: keep waiting on the 3
  in-flight packets while pushing small Claude-owned lemmas.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 04:14 EDT)

- Active jobs (ours): 3/5. All three QUEUED; backlog resurfaced
  (5 non-ours jobs ahead of us).
- **Integrated this tick:** none.
- **Submitted this tick:** none.
- Brief tick — letting the queue drain.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 04:07 EDT)

- Active jobs (ours): 3/5.
- 🎉 **Integrated this tick:** `f9550953` —
  `Periods/ChartLiftApply.lean`. `rfl` one-liner.
- **Submitted this tick (3 refills):**
  - `f8faacda` — `Periods/ChartLiftBoundary.lean`. Boundary-value
    simps (`chartLift_zero`, `chartLift_one`).
  - `bf7d62c4` — `Periods/PathIntegralViaChartLinear.lean`.
    Provisional from-`X` `_neg` and `_smul` (completes provisional
    linearity except `_add`, same Packet F blocker).
  - `82687eb7` — `TraceDegree/PullbackFunSimpApply.lean`. Pointwise
    `_zero/_neg/_smul` apply lemmas for `pullbackFormsFun`.

## Layer status

- **Complex torus layer: complete (sorry-free).**
- **Queue C foundation in place.**
- **Queue D scaffolding (1 opaque, no sorries):** 11 files +
  umbrella; growing.
- **Queue E foundation:** `AnalyticJacobianGroup E X` + umbrella.
- **Queue F:** Recon document.
- **Queue G:** Recon document (`Jacobian/TraceDegree/Recon.lean`)
  inventories `mfderiv`/`ContMDiff` (PRESENT) vs `pullbackForms`/
  `traceForms`/`analyticDegree` (ABSENT); lays out chain-rule for
  pullback, fiber-sum for trace, 6 packets, flags
  `pushforward_pullback` as the strongest multiplicative anti-hack
  theorem.
- All challenge queues (A through G) have at least a recon document
  or production scaffold; Queue H's theorems live in
  `Jacobian/Challenge.lean` directly.

### Queued for next submission round (gated on current batch)

- `pullbackFormsFun_smooth` — Queue G follow-up to `0b8b1163`:
  prove the chain-rule pullback function is `ContMDiff` when `f` is.
  The substantive piece for upgrading to `HolomorphicOneForm E X`.
- `pathIntegralViaChartCorrect` linearity (zero/neg/add) — gated on
  `ee3ce016` + `fe592ee1`.
- Multi-chart `pathIntegralViaCover` definition combining
  `exists_uniform_chart_partition` (from `PathPartition`) with
  chart-local integrals. Needs Claude-owned design step first
  (subpath / affine reparam), then a clean Aristotle packet for
  the well-definedness lemmas.
- Decomposed TorusExample replacement (split into "constant
  function `_ ↦ id` is `ContMDiff`" as a standalone helper, then
  build the section on top), retrying `259b18a1`'s scope.

## Top open correctness item

`chartedForm c ω e v` should equal
`ω.toFun (c.symm e) (D(c.symm)_e v)`, but the current definition
drops the chart-derivative `D(c.symm)_e` and only evaluates the
section at `c.symm e`. Lean accepts the type only because
`TangentSpace I _ = E` trivially. Consequence: `pathIntegralInChart`
is the right integral only when chart transitions are translations
(torus case); it is wrong on a general Riemann surface. Flagged in
the `ChartedForm.lean` docstring and tracked here as the highest-
priority correctness fix. The proper version uses
`mfderiv 𝓘(ℂ, E) (chartedSpaceSelf ...) c.symm e` (or the
inverse-chart partial derivative API).
- Deferred (per the user's explicit guidance and the
  reviewer-acknowledged staging-phase tradeoff): file granularity
  consolidation, naming-convention alignment, and the
  `FullComplexLattice → Submodule + IsZLattice` design change. These
  belong to the eventual Mathlib-prep cleanup, not this phase.

## Planned packets (queued for Aristotle when queue unblocks)

The chart layer is complete; the next layer is `LieAddGroup` smoothness
of `+` and `-` on `quotient V Λ`. Decomposition into Aristotle-sized
packets below. Each packet targets one new file; allowed writes are
that file only; forbidden files always include `Jacobian/Challenge.lean`.

1. **`Jacobian/ComplexTorus/AddSmoothLocal.lean`** — `ContMDiffAt`
   of `(q1, q2) ↦ q1 + q2` at a single point. Strategy: at point
   `(q1, q2)` lift to representatives `v1, v2` via `Function.surjInv`,
   use the chart machinery (the same δ from
   `exists_pos_le_norm_of_discreteTopology` works for both factors),
   and observe that on a small ball the chart-coordinate addition is
   exactly the linear sum on `V × V → V`, then mk back. Re-uses
   `localSection_mk_locally_translate`-style reasoning; no new heavy
   API.

2. **`Jacobian/ComplexTorus/AddSmooth.lean`** — promote (1) to
   `ContMDiff (modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V)
   (modelWithCornersSelf ℂ V) ⊤ (fun p => p.1 + p.2)` and from there
   to a `ContMDiffAdd` instance.

3. **`Jacobian/ComplexTorus/NegSmoothLocal.lean`** — `ContMDiffAt` of
   `q ↦ -q`. Same lift+chart pattern; in chart coordinates negation
   is `x ↦ -x` on `V`, which is `ContDiff ℂ ω`.

4. **`Jacobian/ComplexTorus/NegSmooth.lean`** — promote (3) to
   `ContMDiff` everywhere.

5. **`Jacobian/ComplexTorus/LieAddGroup.lean`** — combine the
   `ContMDiffAdd` instance from (2) and the `contMDiff_neg` from (4)
   into a `LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
   (quotient V Λ)` instance. One- or two-line `where`-clause once the
   pieces are in place.

When the queue unblocks, submit (1) and (3) in parallel (disjoint
write scopes), then (2) and (4), then (5). All five fit the
"prefer simple tactics" guideline.

## General Job Template

```text
Working directory: C:\ver\JacobianChallenge
Target file: <one Lean file>
Allowed writes: only <target file>
Do not edit: Jacobian/Challenge.lean
Task: prove or implement the named declarations below.
Expected verification: lake build <module name>
If blocked: leave the theorem statement unchanged and add a short comment naming
the missing prerequisite.
```

## Queue A: Inventory

Source namespace:

```lean
JacobianChallenge.Inventory
```

Useful declarations:

- `MathlibInventory`
- `inventoryComplete`

Expected output:

- a factual inventory of existing Mathlib declarations at the pinned commit;
- exact file paths and declaration names;
- a list of missing infrastructure.

## Queue B: Complex Tori

Source namespace:

```lean
JacobianChallenge.ComplexTorus
```

Useful declarations:

- `FullComplexLattice`
- `quotient`
- `mk`
- `mk_surjective`
- `map`
- `map_mk`
- `map_id`
- `map_comp`
- `quotientChartedSpaceStatement`
- `quotientIsManifoldStatement`
- `quotientLieAddGroupStatement`

Good first Aristotle packets:

- prove quotient-map universal property lemmas;
- prove `map_mk`, `map_id`, and `map_comp`;
- replace placeholder lattice fields with existing Mathlib predicates if found;
- isolate the exact quotient-manifold theorem needed.

## Queue C: Holomorphic Forms and Genus

Source namespace:

```lean
JacobianChallenge.HolomorphicForms
```

Useful declarations:

- `HolomorphicOneForm`
- `FiniteDimensionalHolomorphicOneForms`
- `analyticGenus`
- `genus_eq_analyticGenus`
- `analyticGenus_eq_zero_iff_homeomorphic_sphere`

Expected packets:

- define holomorphic 1-forms using existing differential-form API;
- prove vector-space structure;
- state finite-dimensionality as a named theorem;
- connect analytic genus to the challenge `genus`.

## Queue D: Periods

Source namespace:

```lean
JacobianChallenge.Periods
```

Useful declarations:

- `IntegralOneCycle`
- `HolomorphicOneFormDual`
- `periodFunctional`
- `periodSubgroup`
- `periodSubgroup_isClosed`
- `periodFullComplexLattice`
- `period_homology_invariance_statement`
- `period_pairing_full_rank_statement`

Expected packets:

- define path/cycle integration;
- prove homology invariance of periods;
- prove period subgroup is closed;
- prove the full-lattice theorem.

## Queue E: Analytic Jacobian

Source namespace:

```lean
JacobianChallenge.AnalyticJacobian
```

Useful declarations:

- `AnalyticJacobian`
- `analyticJacobianEquivChallenge`
- `analyticJacobian_homeomorph_challenge`

Expected packets:

- define Jacobian from the period lattice;
- bridge to the public challenge type;
- handle universe issues deliberately.

## Queue F: Abel-Jacobi

Source namespace:

```lean
JacobianChallenge.AbelJacobi
```

Useful declarations:

- `pathIntegralFunctional`
- `analyticOfCurve`
- `analyticOfCurve_path_independent`
- `analyticOfCurve_self`
- `analyticOfCurve_contMDiff`
- `analyticOfCurve_injective`
- `challenge_ofCurve_eq_analytic`

Expected packets:

- prove path independence modulo periods;
- prove basepoint maps to zero;
- prove holomorphicity;
- prove injectivity for positive genus.

## Queue G: Trace, Degree, Pushforward, Pullback

Source namespace:

```lean
JacobianChallenge.TraceDegree
```

Useful declarations:

- `pullbackForms`
- `traceForms`
- `analyticDegree`
- `trace_pullback_forms`
- `degree_eq_analyticDegree`
- `pullbackForms_preserves_periods`
- `traceForms_preserves_periods`
- `analyticDegree_comp`
- `pushforward_pullback_from_trace`

Expected packets:

- define pullback of forms;
- define trace of forms;
- prove the trace-pullback identity;
- define degree compatibly;
- descend maps to Jacobians.

## Queue H: Anti-Hack Theorems

Source namespace:

```lean
JacobianChallenge.AntiHack
```

Useful declarations:

- `genus_zero_topological_sphere`
- `positive_genus_nontrivial_jacobian`

Expected packets:

- prove or trace dependencies for the anti-hack theorems;
- keep these theorems separate from convenience API;
- do not weaken their statements.
