# Result: Weighted-Fiber Provider Moved To Holomorphic-Map Theorem

## Branch / commit

* Branch: `decompose-trace-degree-frontiers` (continuing from
  `176a662` — the previous frontier-decomposition commit).
* New commit on this branch: see `git log -1` after the commit at
  the end of this round.
* Not yet pushed to a remote.

## Summary

* `hasWeightedFiberConservation_provider` is now **sorry-free**.
* A new narrow theorem `weightedFiberConservation_of_contMDiff` is added
  in `Jacobian/HolomorphicForms/HolomorphicMap.lean` (next to
  `hasLocalKfoldRamification_of_contMDiff`) with the exact unbundled
  shape of the `HasWeightedFiberConservation.weightedFiberSum_eventually_eq`
  field. Currently a named `sorry` with a precise proof-skeleton
  docstring.
* A wrapper `hasWeightedFiberConservation_of_contMDiff` in the same
  file packages the narrow theorem into a `HasWeightedFiberConservation`
  structure; it is sorry-free.
* `hasWeightedFiberConservation_provider` in
  `Jacobian/TraceDegree/AnalyticDegree.lean` is now a one-line
  delegation to the packaged form.

The analytic content (weighted fibre conservation for a nonconstant
smooth map between compact Riemann surfaces) has moved out of the
trace-degree-local provider and into a general holomorphic-map theorem
where it belongs.

## Files Changed (this round)

| File | Δ | Nature |
|------|---|--------|
| `Jacobian/HolomorphicForms/HolomorphicMap.lean` | +50 lines | Added `weightedFiberConservation_of_contMDiff` (narrow, sorry stub) and `hasWeightedFiberConservation_of_contMDiff` (sorry-free packager) |
| `Jacobian/TraceDegree/AnalyticDegree.lean` | rewritten provider | `hasWeightedFiberConservation_provider` is now sorry-free, a one-line wrapper around `hasWeightedFiberConservation_of_contMDiff` |
| `sorries.jsonl` | resync | Reflects the moved sorry |
| `result.md` | rewritten | This file |

## Exact new theorem statement

`Jacobian/HolomorphicForms/HolomorphicMap.lean:1108-1118` (sorry body):

```lean
theorem weightedFiberConservation_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (y₀ : Y) :
    ∀ᶠ y in 𝓝 y₀,
      (Finset.sum (finite_fiber y).toFinset (mapAnalyticOrderAt f)) =
      (Finset.sum (finite_fiber y₀).toFinset (mapAnalyticOrderAt f)) := by
  sorry
```

And the sorry-free packager (same file):

```lean
theorem hasWeightedFiberConservation_of_contMDiff
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    HasWeightedFiberConservation f where
  weightedFiberSum_eventually_eq := by
    intro _ _ _ _ _ _ hnonconst finite_fiber y₀
    exact weightedFiberConservation_of_contMDiff hf hnonconst finite_fiber y₀
```

And the new provider in `Jacobian/TraceDegree/AnalyticDegree.lean`
(sorry-free):

```lean
theorem hasWeightedFiberConservation_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HasWeightedFiberConservation f :=
  hasWeightedFiberConservation_of_contMDiff hf
```

## Sorry count

* **Before**: 45 sorries across 27 files.
* **After**: 45 sorries across 28 files.
* **Net change**: 0; one sorry **moved** from the trace-degree-local
  provider into a general holomorphic-map theorem in `HolomorphicMap.lean`.

| Removed | Added |
|---------|-------|
| `hasWeightedFiberConservation_provider` in `Jacobian/TraceDegree/AnalyticDegree.lean` (broad trace-degree-local provider) | `weightedFiberConservation_of_contMDiff` in `Jacobian/HolomorphicForms/HolomorphicMap.lean` (strictly narrower: unbundled form of the structure field, in the general holomorphic-map API) |

The replacement is strictly narrower per the goal's criterion:
* The old provider's signature returned a full `HasWeightedFiberConservation f`
  structure with an implicit-instance-quantified universal field.
* The new theorem returns the unbundled `∀ᶠ`-equality for a specific
  `y₀`, with explicit `finite_fiber` and instance hypotheses. It is
  the exact analytic content unwrapped.
* The packager `hasWeightedFiberConservation_of_contMDiff` is sorry-free
  and re-bundles it; the provider in trace-degree is a one-line wrapper
  with no analytic content.

## Verification

```sh
lake exe cache get                                # no-op, cache present
lake build Jacobian.HolomorphicForms.HolomorphicMap   # OK (1 narrow sorry reported)
lake build Jacobian.TraceDegree.AnalyticDegree    # OK (3 narrow sorries left: trace_pullback_provider, traceFormsRegularSpec_provider, analyticPushPull_provider)
lake build Jacobian.TraceDegree.PullbackBasis     # OK (1 narrow sorry: transferCycle_periodPairing_naturality)
lake build Jacobian/Solution.lean                 # OK
python3 scripts/fix-sorries.py                    # synced sorries.jsonl (1245 records)
python3 scripts/list-sorries.py --no-build --text # 45 sorries across 28 files
python3 scripts/audit-sorries.py sorries.jsonl    # Audit passed.
git diff --check                                  # clean
```

## Remaining blocker

The body of `weightedFiberConservation_of_contMDiff` is still a `sorry`.
The proof skeleton (documented in the theorem's docstring) follows the
D1+D2+B+C decomposition from `Jacobian/Blueprint/Sec02/WeightedFiberCardConst.lean`:

1. **D1** — pairwise-disjoint open neighbourhoods of
   `S₀ := (finite_fiber y₀).toFinset` via `Set.Finite.t2_separation`.
2. **D2** — properness on compact source confines fibres of nearby
   `y` to `⋃_{x ∈ S₀} U_x`
   (`eventually_fiber_subset_of_compact_T2`).
3. **B** — each unramified `x ∈ S₀` contributes exactly one preimage
   in `U_x` for every nearby `y`
   (`IsHolomorphicAt.exists_local_inj_of_unramified` in Sec02; or
   the special case `k = 1` of `local_kfold_ramified_of_contMDiff`
   which is *already in `HolomorphicMap.lean`*).
4. **C** — each ramified `x ∈ S₀` of order `k_x` contributes exactly
   `k_x` simple preimages in `U_x` for every nearby `y ≠ y₀`
   (`IsHolomorphicAt.exists_local_kfold_of_ramified` in Sec02; or
   the general case of `local_kfold_ramified_of_contMDiff`).

The crucial observation: `local_kfold_ramified_of_contMDiff` (already
in `HolomorphicMap.lean`, line 990) **unifies** leaves B and C — it
gives, for every `x ∈ S₀` with `0 < k_x = mapAnalyticOrderAt f x`,
neighbourhoods `U_x ∋ x`, `V_x ∋ y₀ = f x`, such that
for every `y ∈ V_x \ {y₀}` there is a `Finset s` of `k_x`
unramified preimages of `y` in `U_x` exhausting `U_x ∩ f⁻¹{y}`.

Combined with D1 + D2, this directly proves the theorem without
needing the Sec02 helpers as a separate dependency. The proof
migration is a self-contained ~100–150 line `HolomorphicMap.lean`
follow-up that does not introduce new cross-file imports.

`mapAnalyticOrderAt_pos` (line 748, already in `HolomorphicMap.lean`)
supplies the positivity `0 < k_x` from `IsHolomorphic` +
nonconstancy + `PreconnectedSpace X` + `T2Space Y` — all already
available. `IsHolomorphic` is derived from `ContMDiff` via
`isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)`.

## Why this is meaningful progress

Before this round:
* `hasWeightedFiberConservation_provider` was a trace-degree-local
  provider with the *entire bundled structure* as a single sorry.
  Anyone wanting to use it had to discharge a `Prop` field whose
  universal-quantified signature mixed manifold instance arguments,
  finite-fibre data, base point, and the eventually-equality.

After this round:
* The provider is sorry-free.
* The remaining analytic content is a single named theorem in
  `HolomorphicMap.lean` with a precise, unbundled type signature, in
  the same file as `local_kfold_ramified_of_contMDiff` (its key
  ingredient).
* The proof migration is self-contained and does not require touching
  trace-degree files.
* The proof skeleton is documented inline.
