# Result: Weighted-Fiber Provider Fully Proved (Rebased on origin/main)

## Branch / commit

* Branch: `decompose-trace-degree-frontiers`.
* Three commits on top of `origin/main` (`aa0f976` — PR #203
  genus-zero route-data refinement; contains origin/main's independent
  proof of `weightedFiberConservation_of_contMDiff`):
  1. `fe02a5a` — *Decompose trace–degree push-pull frontiers into narrow leaves*
  2. `9b7e7b4` — *Move weighted-fiber conservation out of the trace-degree provider*
     (post-rebase: adds the `hasWeightedFiberConservation_of_contMDiff`
     packager since origin/main only added the unbundled theorem)
  3. `4e5ce81` — *Prove weightedFiberConservation_of_contMDiff*
     (post-rebase: only updates `result.md`, since origin/main's
     `da8eecf` independently landed the canonical proof of
     `weightedFiberConservation_of_contMDiff`; the rebase took
     origin/main's proof and dropped my divergent proof)
* Not yet pushed to a remote.

## Summary

**Best outcome achieved.** `hasWeightedFiberConservation_provider`,
`hasWeightedFiberConservation_of_contMDiff`, and
`weightedFiberConservation_of_contMDiff` are all **sorry-free**.

The proof of `weightedFiberConservation_of_contMDiff` is from
origin/main's `da8eecf` (independently authored, using essentially the
same blueprint as mine). My contribution that survives the rebase:

* The trace-degree frontier decomposition (commit `fe02a5a`).
* The `hasWeightedFiberConservation_of_contMDiff` packager in
  `HolomorphicMap.lean` (commit `9b7e7b4`) — origin/main only added
  the unbundled `weightedFiberConservation_of_contMDiff`; the
  packager that wraps it into a `HasWeightedFiberConservation`
  structure is new from my branch.
* The sorry-free wiring of `hasWeightedFiberConservation_provider` in
  `AnalyticDegree.lean` (in commit `9b7e7b4`), a one-line wrapper
  around the packager.

`#print axioms` confirms only `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`, no surprise axioms.

## Files Changed (cumulative, vs `origin/main`)

```
 Jacobian/HolomorphicForms/HolomorphicMap.lean |  20 ++
 Jacobian/TraceDegree/AnalyticDegree.lean      | 338 ++++++++++++++++----------
 Jacobian/TraceDegree/PullbackBasis.lean       |  48 +++-
 result.md                                     | (this file)
 sorries.jsonl                                 | (resync)
```

The 20 lines added to `HolomorphicMap.lean` are exactly the
`hasWeightedFiberConservation_of_contMDiff` packager — origin/main's
`weightedFiberConservation_of_contMDiff` provides the unbundled
analytic content; my packager bundles it into the structure form
expected by `HasWeightedFiberConservation` consumers.

## Was `hasWeightedFiberConservation_provider` proved?

**Yes — fully sorry-free** via a transitive chain that ends in
origin/main's analytic proof:

```lean
-- Jacobian/TraceDegree/AnalyticDegree.lean (my commit):
theorem hasWeightedFiberConservation_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HasWeightedFiberConservation f :=
  hasWeightedFiberConservation_of_contMDiff hf

-- Jacobian/HolomorphicForms/HolomorphicMap.lean (my commit, packager):
theorem hasWeightedFiberConservation_of_contMDiff
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    HasWeightedFiberConservation f where
  weightedFiberSum_eventually_eq := by
    intro _ _ _ _ _ _ hnonconst finite_fiber y₀
    exact weightedFiberConservation_of_contMDiff hf hnonconst finite_fiber y₀

-- Jacobian/HolomorphicForms/HolomorphicMap.lean (from origin/main `da8eecf`):
theorem weightedFiberConservation_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (y₀ : Y) :
    ∀ᶠ y in 𝓝 y₀,
      (Finset.sum (finite_fiber y).toFinset (mapAnalyticOrderAt f)) =
      (Finset.sum (finite_fiber y₀).toFinset (mapAnalyticOrderAt f)) := by
  -- Origin/main's D3 assembly using local_kfold_ramified_of_contMDiff
  ...
```

## Sorry count

* **Pre-rebase tip on old base**: 44 sorries across 27 files.
* **After origin/main absorbed PR #203 (without my branch)**: 41 sorries across 25 files.
* **After my branch rebased on top**: 39 sorries across 25 files.
* **Net contribution from my branch (vs origin/main)**: −2 sorries.

Remaining sorries in my touched files (the four narrow trace-degree
leaves):

| File | Remaining sorry |
|------|-----------------|
| `Jacobian/TraceDegree/AnalyticDegree.lean` | `trace_pullback_provider` |
| `Jacobian/TraceDegree/AnalyticDegree.lean` | `analyticPushPull_provider` |
| `Jacobian/TraceDegree/AnalyticDegree.lean` | `traceFormsRegularSpec_provider` |
| `Jacobian/TraceDegree/PullbackBasis.lean` | `transferCycle_periodPairing_naturality` |

## Verification

```sh
git fetch origin main                                # aa0f976
git rebase origin/main                               # resolved conflicts in HolomorphicMap.lean and sorries.jsonl
lake exe cache get                                   # no-op
lake build Jacobian.HolomorphicForms.HolomorphicMap     # OK
lake build Jacobian.TraceDegree.AnalyticDegree       # OK
lake build Jacobian.TraceDegree.PullbackBasis        # OK
lake build Jacobian/Solution.lean                    # OK (3836 jobs)
python3 scripts/fix-sorries.py                       # 1250 records
python3 scripts/list-sorries.py --no-build --text    # 39 sorries across 25 files
python3 scripts/audit-sorries.py sorries.jsonl       # Audit passed.
git diff --check                                     # clean
```

`#print axioms` for the new sorry-free theorems:

* `weightedFiberConservation_of_contMDiff` (from origin/main) —
  `propext`, `Classical.choice`, `Quot.sound`
* `hasWeightedFiberConservation_of_contMDiff` (mine, packager) —
  `propext`, `Classical.choice`, `Quot.sound`
* `hasWeightedFiberConservation_provider` (mine, trace-degree) —
  `propext`, `Classical.choice`, `Quot.sound`

No `sorryAx`. No surprise axioms.

## Rebase notes

Origin/main's PR #203 (commits `30e450c..aa0f976`) touched
`Periods/`, `StageA/`,
`HolomorphicForms/{GenusZeroClassification,HarmonicFunctions,Meromorphic,
MeromorphicToCp1,RiemannRoch,SinglePoleLift}.lean`, `Solution.lean`,
and most importantly added origin/main's own
`weightedFiberConservation_of_contMDiff` proof in `HolomorphicMap.lean`
(commit `da8eecf`).

Conflict resolution:

* `HolomorphicMap.lean`: convergent change with origin/main on
  `weightedFiberConservation_of_contMDiff`. Took origin/main's proof
  (uses the canonical helpers `local_kfold_witness_weighted_sum` and
  `finite_toFinset_sum_eq_of_set_eq` already in the file). Kept my
  `hasLocalKfoldRamification_of_contMDiff` (still needed) and added
  the `hasWeightedFiberConservation_of_contMDiff` packager.
* `sorries.jsonl`: regenerated by `scripts/fix-sorries.py` after the
  rebase completed.
* `result.md`: rewritten (this file).

## Why this is meaningful progress

The decomposition of the trace-degree frontiers into narrow leaves
(commit `fe02a5a`, unchanged from pre-rebase) plus the
`hasWeightedFiberConservation_of_contMDiff` packager and the
sorry-free wiring of `hasWeightedFiberConservation_provider`
together mean:

* `analyticTraceDegreeSpec_frontier` is no longer a monolithic black
  box — it's an assembly over four named narrow providers.
* `hasWeightedFiberConservation_provider` is sorry-free, transitively
  reducing to `weightedFiberConservation_of_contMDiff` (proved in
  origin/main).
* The remaining four narrow leaves — `trace_pullback_provider`,
  `analyticPushPull_provider`, `traceFormsRegularSpec_provider`,
  `transferCycle_periodPairing_naturality` — remain as their own
  well-defined targets for subsequent work, each with a crisp
  mathematical statement.

The convergent independent proof from origin/main and from my branch
is encouraging — both implementations landed essentially the same
blueprint (D1+D2+B+C) using the same `local_kfold_ramified_of_contMDiff`
infrastructure. Origin/main's proof is preserved in the rebased tree;
my divergent proof was dropped (no functional loss).
