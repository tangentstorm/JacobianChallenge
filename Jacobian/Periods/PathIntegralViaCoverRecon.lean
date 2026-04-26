import Jacobian.Periods.PathPartition
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Reconnaissance: multi-chart path integral

Queue D design document. Sketches the construction of
`pathIntegralViaCover ω γ` — the path integral of a holomorphic 1-form
along a path that may cross chart boundaries, by combining the
chart-cover partition (`exists_uniform_chart_partition`) with the
chart-local integral (`pathIntegralViaChartCorrect`).

This file contains no production declarations; it is not re-exported
by the `Jacobian.Periods` umbrella.

## Inputs available

- `exists_uniform_chart_partition E γ`
  (`Jacobian/Periods/PathPartition.lean`): for `γ : C(unitInterval, X)`,
  produces `n ≥ 1` and `pickChart : Fin n → X` such that for every
  `i : Fin n` and every `t` in `[i/n, (i+1)/n]`, `γ t` lies in
  `(chartAt E (pickChart i)).source`.

- `pathIntegralViaChartCorrect c ω γ h`
  (`Jacobian/Periods/PathIntegralViaChartCorrect.lean`): given a chart
  `c : OpenPartialHomeomorph X E`, a 1-form `ω`, and a path `γ` whose
  range is in `c.source`, returns the chart-local integral `∫_γ ω`
  using the genuine `mfderiv`-aware pullback.

- `chartAt E x : OpenPartialHomeomorph X E` is Mathlib's chart at `x`.
  In our setting it is an `OpenPartialHomeomorph` thanks to the
  `[ChartedSpace E X]` instance (the source `(chartAt E x).source` is
  open and contains `x`).

## What's missing

We need a way to carve `γ : Path a b` (where `a b : X`) into `n`
sub-paths
```
γᵢ : Path (γ ⟨i/n, ...⟩) (γ ⟨(i+1)/n, ...⟩)
```
each lying inside `(chartAt E (pickChart i)).source`, then sum the
chart-local integrals.

Mathlib's `Path` API has `Path.trans`, `Path.symm`, `Path.refl`,
`Path.map'`, `Path.delayReflRight`/`delayReflLeft`, but no
*generic* affine-reparametrization-based subpath operation. We will
need a small helper:

```text
Path.subpath (γ : Path a b) (s t : ℝ) (0 ≤ s ≤ t ≤ 1) :
  Path (γ ⟨s, ...⟩) (γ ⟨t, ...⟩)
```

defined via the affine map `unitInterval → unitInterval`,
`u ↦ ⟨s + u * (t - s), ...⟩`, composed with `γ`.

## Construction sketch

```text
noncomputable def pathIntegralViaCover
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) : ℂ := by
  -- Step 1: extract a uniform chart partition of γ as a continuous map.
  obtain ⟨n, hn, pickChart, hcov⟩ :=
    exists_uniform_chart_partition E γ.toContinuousMap
  -- Step 2: for each i : Fin n, build the subpath
  --   γᵢ := γ.subpath (i/n) ((i+1)/n)
  -- and verify range γᵢ ⊆ (chartAt E (pickChart i)).source via hcov.
  -- Step 3: sum:
  --   ∑ i : Fin n, pathIntegralViaChartCorrect
  --                  (chartAt E (pickChart i)) ω γᵢ (range_proof i)
  exact ...
```

## Open questions / well-definedness

1. **Independence of partition.** Different choices of partition or
   chart picks should yield the same integral. This requires a
   chart-transition lemma: on the overlap of two charts, the two
   chart-local integrals over the same path agree (by smoothness of
   the transition map and the chain rule for `mfderiv`). This is the
   first major theorem after the definition lands.

2. **Linearity.** Linearity in `ω` follows from
   `pathIntegralViaChartCorrect_zero/_neg/_add/_smul` (the latter
   is `9c8842f9` in flight; `_neg/_add` is `fe592ee1`).

3. **Reverse path / refl.** `_refl` and `_symm` for the multi-chart
   integral follow from the chart-local lemmas plus a partition
   shuffle (reversing the range and the partition).

4. **Path concatenation.** `pathIntegralViaCover` of `γ.trans γ'`
   should equal the sum of the two integrals. This requires careful
   handling of partitions on `[0, 1/2]` vs `[1/2, 1]`.

## Aristotle-sized packets (after the local design lands)

A. `Jacobian/Periods/PathSubpath.lean` — define `Path.subpath` via
   `unitInterval → unitInterval` affine reparam. Tactic-level proofs
   of `subpath 0 1 = γ`, `subpath_continuous`, source/target.

B. `Jacobian/Periods/PathIntegralViaCover.lean` — define
   `pathIntegralViaCover ω γ` per the sketch above (Claude-owned;
   too design-heavy for a single Aristotle packet).

C. `Jacobian/Periods/PathIntegralViaCoverRefl.lean` —
   `pathIntegralViaCover_refl ω a = 0`. Likely follows from
   `Finset.sum_zero` after each segment-integral collapses to zero.

D. `Jacobian/Periods/PathIntegralViaCoverLinear.lean` — zero/neg/add/smul
   for `pathIntegralViaCover`, by distributing through `Finset.sum`.

E. The chart-transition lemma (well-definedness) — substantial; gates
   on the smoothness theorem for `chartedFormPullback` (or for the
   composite chart transition). May need to be split further.

## Convention

Per the project's recon convention, this file builds standalone but
provides no production declarations. The `Jacobian.Periods` umbrella
does not re-export it.
-/

namespace JacobianChallenge.Periods

/-- Marker so this file produces a non-empty namespace and clearly
participates in the build graph. Not exported. -/
def pathIntegralViaCoverReconStub : Unit := ()

end JacobianChallenge.Periods
