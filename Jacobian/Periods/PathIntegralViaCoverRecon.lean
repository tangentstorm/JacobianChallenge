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

## What's available (revised)

We need a way to carve `γ : Path a b` (where `a b : X`) into `n`
sub-paths
```
γᵢ : Path (γ ⟨i/n, ...⟩) (γ ⟨(i+1)/n, ...⟩)
```
each lying inside `(chartAt E (pickChart i)).source`, then sum the
chart-local integrals.

**Update:** Mathlib v4.28.0 already has `Path.subpath` in
`Mathlib.Topology.Subpath`:

```text
def Path.subpath (γ : Path a b) (t₀ t₁ : I) : Path (γ t₀) (γ t₁) where
  toFun := γ ∘ (subpathAux t₀ t₁)
  ...
```

with `subpathAux t₀ t₁ : I → I = (1 - s) * t₀ + s * t₁` (convex
combination, sends `0 ↦ t₀`, `1 ↦ t₁`). Useful API:

* `Path.subpath_zero_one γ`: `γ.subpath 0 1 = γ.cast …` (full path).
* `Path.subpath_self γ t`: `γ.subpath t t = Path.refl (γ t)`.
* `Path.range_subpath γ t₀ t₁`: `range (γ.subpath t₀ t₁) =
  γ '' (uIcc t₀ t₁)`.
* `Path.symm_subpath γ t₀ t₁`: `(γ.subpath t₀ t₁).symm =
  γ.subpath t₁ t₀`.
* `Path.Homotopy.concatSubpath` (in the same file): subdivide a
  single subpath as a homotopy class equal to a chain of sub-subpaths.

So we don't need to write a `Path.subpath` helper — packet A in the
old plan is unnecessary.

## Construction sketch

The cleanest split is two definitions: a "given partition" version
and the wrapper that picks a partition.

```text
-- Helper: i/n as a unit-interval point, given i ≤ n.
noncomputable def Periods.divFinIcc (n : ℕ) (hn : 0 < n)
    (i : ℕ) (hi : i ≤ n) : unitInterval :=
  ⟨(i : ℝ) / n, by
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hi⟩

-- "Given partition" version (Claude-owned design choice).
noncomputable def pathIntegralViaCoverWith
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ)/n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1)/n →
      γ t ∈ (chartAt E (pickChart i)).source) : ℂ :=
  ∑ i : Fin n,
    pathIntegralViaChartCorrect (chartAt E (pickChart i)) ω
      (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                 (divFinIcc n hn (i.val + 1) i.isLt))
      (by
        -- range γᵢ ⊆ chart.source via Path.range_subpath + hcov
        rw [Path.range_subpath]
        intro x ⟨t, ht, rfl⟩
        -- ht : t ∈ uIcc (divFinIcc n hn i ...) (divFinIcc n hn (i+1) ...)
        -- hcov needs t.val ∈ [i/n, (i+1)/n]
        sorry)

-- Wrapper: choose any partition via Classical.
noncomputable def pathIntegralViaCover
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) : ℂ :=
  let p := (exists_uniform_chart_partition E γ.toContinuousMap).choose_spec
  let _ := p.choose      -- 0 < n
  let p' := p.choose_spec
  let pickChart := p'.choose
  let hcov := p'.choose_spec
  pathIntegralViaCoverWith ω γ
    ((exists_uniform_chart_partition E γ.toContinuousMap).choose)
    p.choose pickChart hcov
```

The `sorry` in the range proof is the only nontrivial step — once
that is discharged, the definition is total. The proof obligation:
given `t ∈ uIcc (divFinIcc n hn i ...) (divFinIcc n hn (i+1) ...)`,
show `i/n ≤ t.val ≤ (i+1)/n`. Since `i/n ≤ (i+1)/n`, the unordered
`uIcc` collapses to `Icc`, and the bounds follow from
`Set.mem_Icc.mp` plus the `divFinIcc.val = i/n` definitional unfold.

## Discovered blocker: `CurveIntegrable` for chartedFormPullback

Mathlib's `curveIntegral_add f g γ` requires `CurveIntegrable f γ` and
`CurveIntegrable g γ` hypotheses (otherwise the equation fails under
the convention that non-integrable curves integrate to zero). This
blocks the `_add` linearity lemma for `pathIntegralInChartCorrect`
(salvaged version with only `_neg` lives in
`Jacobian/Periods/PathIntegralChartCorrectLinear.lean`).

**Required helper (Packet F):** prove
```text
chartedFormPullback_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    CurveIntegrable (chartedFormPullback c ω) γ
```
which reduces (via `CurveIntegrable.continuous` or similar Mathlib
helper) to continuity of `chartedFormPullback c ω : E → E →L[ℂ] ℂ`,
which in turn follows from continuity (in fact analyticity) of `ω`
and continuity of `mfderiv c.symm`.

Once this lands, `_add` for `pathIntegralInChartCorrect` follows by
the same proof template Aristotle attempted in `fe592ee1` (which
landed `_neg` cleanly but had to `sorry` the integrability assumptions
of `_add`).

`curveIntegral_neg` does NOT need integrability (a single curve), so
`_neg` was unblocked.

`curveIntegral_smul` also does not need integrability (scaling a
non-integrable function by k still gives a non-integrable function
which integrates to zero, matching `k • 0 = 0`), so the in-flight
`9c8842f9` (`pathIntegralInChartCorrect_smul`) should not hit this
blocker.

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

## Aristotle-sized packets (revised, with progress notes)

~~A. `Jacobian/Periods/PathSubpath.lean`~~ — superseded by Mathlib's
   `Path.subpath`. No packet needed.

✓ B. `Jacobian/Periods/PathIntegralViaCover.lean` — `pathIntegralVia-
   CoverWith` (parameterised) **landed** as Claude-owned local work
   (commit 7a691e8). The unparameterised wrapper
   `pathIntegralViaCover` lives in
   `Jacobian/Periods/PathIntegralViaCoverPick.lean`.

✓ C. **Multi-chart `_refl` (`pathIntegralViaCoverWith_refl`):** in
   flight as `ea9c5d7a`, gated on `5d2035c3`
   (`chartLift_refl_subpath`). Naive proof was blocked by a
   dependent-rewrite issue when the range hypothesis depended on the
   path; the bridge helper sidesteps that.

✓ D. **Linearity of `pathIntegralViaCoverWith`:** zero (`PathIntegralVia-
   CoverZero.lean`), neg (`PathIntegralViaCoverNeg.lean`), smul
   (`PathIntegralViaCoverSmul.lean`) all landed. Add still gated on
   Packet F (integrability).

   **Linearity of `pathIntegralViaCover` (unparameterised):** zero,
   neg, smul landed (`PathIntegralViaCoverPickSimp.lean`,
   `PathIntegralViaCoverPickSmul.lean` in flight as `ad85aa10`). The
   key insight — `Classical.choose` only depends on `γ`, not `ω` —
   makes both sides use the same picked partition.

E. The chart-transition lemma (well-definedness) — substantial; gates
   on the smoothness theorem for `chartedFormPullback` (or for the
   composite chart transition). May need to be split further. Mathlib's
   `Path.Homotopy.concatSubpath` (in `Mathlib.Topology.Subpath`) is a
   relevant building block: it shows that concatenating subpaths is
   homotopic to a single subpath, which is the homotopy-level analog
   of "the integral does not depend on partition."

F. **`Jacobian/Periods/ChartedFormPullbackCurveIntegrable.lean`** —
   `CurveIntegrable (chartedFormPullback c ω) γ` for any path. This
   unblocks `_add` (and the multi-chart well-definedness via
   `curveIntegral_add` over partition pieces). The proof should
   reduce to continuity of `chartedFormPullback c ω` and a
   `CurveIntegrable.continuousOn` (or similar) helper.

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
