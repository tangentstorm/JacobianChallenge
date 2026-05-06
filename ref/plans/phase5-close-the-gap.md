# Plan: Closing the gap in `pathIntegralViaChartCorrect_pullbackFormsBundledLM`

## Current state (after PR #119)

* `Jacobian/Periods/ChartedFormPullbackChainRule.lean` — sorry-free.
  Establishes the algebraic chart-level chain rule.
* `Jacobian/Periods/PathIntegralViaChartCorrectPullback.lean` — 1 sorry.
  The differentiable case is fully discharged. The remaining `sorry` covers
  the pathological case where `γ_X.extend` is non-differentiable at `t` and
  `ψ ∘ γ_X.extend` IS differentiable at `t` (with non-zero derivative `v`).

## Mathematical content of the gap

In the pathological case, my analysis establishes:

1. `γ_X.extend t` must be at a critical point of `ψ` (otherwise `ψ` is locally
   invertible, forcing `γ_X.extend` differentiable by `ψ⁻¹` smooth — contradicts
   `hd`).
2. At critical points of `ψ`, `mfderiv ψ (γ_X.extend t) = 0`.
3. From `HasFDerivAt ψ 0 (γ_X.extend t)` and `HasDerivWithinAt (ψ ∘ γ_X.extend) v I t`
   with `v ≠ 0`:
   ```
   |(ψ(γ_X(s)) - ψ(γ_X(t)))/(s - t)| ≤ ε |γ_X(s) - γ_X(t)|/|s - t|   (ε arbitrary)
   |((ψ ∘ γ_X)(s) - (ψ ∘ γ_X)(t))/(s - t)| ≥ |v|/2                  (s near t)
   ```
   These force `lim_{s → t} |γ_X.extend(s) - γ_X.extend(t)|/|s - t| = ∞`.

The contradiction holds for Lipschitz `γ_X.extend` (bounded diff quotient) but
**not for arbitrary continuous γ_X.extend** (sub-Hölder fractal paths can
satisfy the divergent diff quotient condition).

## Strategy A — Lipschitz hypothesis on γ

### Approach

Add `(K : ℝ≥0) (hγ_Lip : LipschitzWith K γ.toFun)` to
`pathIntegralViaChartCorrect_pullbackFormsBundledLM`. Then in the bad case:

1. `cX` is smooth on `cX.source` ⊇ `range γ` (compact). So `cX` is `LipschitzOnWith L`
   for some `L` on the compact range.
2. `γ_X.extend = cX ∘ γ.extend` is `LipschitzWith (L * K)` on `[0, 1]`.
3. So `|γ_X.extend(s) - γ_X.extend(t)|/|s - t| ≤ L * K` (bounded).
4. Combined with `HasFDerivAt ψ 0 (γ_X.extend t)`:
   `|((ψ ∘ γ_X.extend)(s) - (ψ ∘ γ_X.extend)(t))/(s - t)| ≤ ε · L * K`
   for any ε > 0 and s near t.
5. So `HasDerivWithinAt (ψ ∘ γ_X.extend) 0 I t` (the derivative is 0).
6. By uniqueness, `derivWithin (ψ ∘ γ_X.extend) I t = 0`. Goal discharged.

### Cascade

The hypothesis must propagate through:

* `pathIntegralViaCoverWith_pullback_via_common_partition` — pass `hγ_Lip`,
  use `Path.subpath_lipschitz` (a new helper) to get Lipschitz for each
  segment.
* `pathIntegralViaCoverWith_pullbackFormsBundledLM` — pass `hγ_Lip` through
  to the segment lemma.
* `pathIntegralViaCover_pullbackFormsBundledLM` — pass `hγ_Lip` through.
* `pathIntegralViaCover_pullback_chart_segment` — pass `hγ_Lip`.

Higher up, `IntegralOneCycle`-level period naturality theorems would
either require `LipschitzWith K` on representative singular simplices, or
restrict to a "smooth representative" subcomplex that's quasi-isomorphic
to the full singular complex.

### New helper lemmas (Mathlib-style)

```lean
-- In a new file Jacobian/Periods/PathLipschitz.lean
lemma Path.subpath_lipschitzWith
    {a b : X} (γ : Path a b) (K : ℝ≥0) (hγ : LipschitzWith K γ.toFun)
    (t₀ t₁ : unitInterval) :
    LipschitzWith (K * (Real.toNNReal |t₁ - t₀|)) (γ.subpath t₀ t₁).toFun
```

```lean
-- Lipschitz transport through the chart (helper for the chain-rule proof)
lemma chartLift_lipschitzOn
    (c : OpenPartialHomeomorph X ℂ) (γ : Path a b)
    (h : range γ ⊆ c.source) (K : ℝ≥0) (hγ : LipschitzWith K γ.toFun) :
    ∃ L : ℝ≥0, LipschitzOnWith L (chartLift c γ h).extend (Set.Icc 0 1)
```

The first uses linearity of `subpathAux`. The second requires `c` Lipschitz
on the compact range of `γ`, which follows from smoothness on the open
source.

### Effort estimate

* ~50 lines for `Path.subpath_lipschitzWith` and `chartLift_lipschitzOn`.
* ~30 lines to discharge the sorry using the Lipschitz bound + the chain
  rule contradiction argument.
* Cascading API updates: ~5-10 lemma signatures, ~50 lines of changes.

**Total: ~150 lines.** Conceptually clean.

## Strategy B — Measure-zero argument via analyticity

### Approach

Keep the lemma's signature as-is. Switch from
`intervalIntegral.integral_congr` (pointwise) to
`intervalIntegral.integral_congr_ae` (a.e.). Show the bad set has measure 0:

The bad set is contained in
`γ_X.extend⁻¹({z : mfderiv ψ z = 0}) ∩ {t : γ_X.extend not diff at t}`.

For analytic non-constant ψ : ℂ → ℂ (which our chart-transition is, by
holomorphy of f and the analytic chart-changes):

* The critical set `{z : mfderiv ψ z = 0}` is the zero set of the analytic
  function `ψ'`. By the identity theorem, this is either ALL of cX.target
  (if ψ is constant) or a discrete (countable) set.
* The non-constant case: critical set is countable.
* Preimage under continuous γ_X.extend: countable union of level sets.

For each level set `Lc := γ_X.extend⁻¹({c})` (c critical):
* If γ_X.extend is constant on a positive-measure subset of `Lc`:
  γ_X.extend is differentiable there with derivative 0. So
  `Lc ∩ {non-diff}` has measure 0.
* If γ_X.extend isn't constant on any positive-measure subset of `Lc`:
  level sets of non-constant continuous functions are... still possibly
  positive-measure (fat Cantor case).

**This argument has a gap**: for Cantor-like γ_X.extend, level sets can have
positive measure, and within those level sets the non-differentiable subset
can be the whole level set.

### Refinement

The argument **does** work if we additionally know γ_X.extend is
**absolutely continuous** (AC): by Lusin's N condition, AC functions map
measure-zero sets to measure-zero sets. Conversely, AC ⇒ differentiable
a.e. (Lebesgue). Combined: bad set has measure 0.

So Strategy B requires AC γ_X.extend, which is essentially equivalent to
Lipschitz (or BV + continuous = AC).

### Effort estimate

* New helper: γ_X.extend is AC ⇔ γ.extend is AC (using cX smooth Lipschitz).
* Argue critical set of analytic ψ has measure 0 in cX.target.
* Argue Lusin N: AC γ_X.extend ⇒ preimage of measure-0 set has measure 0.
* Argue Lebesgue: AC γ_X.extend ⇒ differentiable a.e.
* Combine: bad set has measure 0.
* Use `integral_congr_ae` to discharge.

This is **more complex** than Strategy A and ultimately requires the same
hypothesis (AC ≈ Lipschitz).

**Total: ~250+ lines.** Less clean.

## Strategy C — Hybrid: integrability case-split

### Approach

Use `intervalIntegral.integral_undef` for the non-integrable case. Specifically:

```
by_cases hint : CurveIntegrable (chartedFormPullback cX (pullback ...)) γ_X
case neg =>
  -- LHS = 0 by integral_undef.
  -- Show RHS = 0 too. Need symmetry of integrability under ψ.
  rw [integral_undef hint]
  -- For RHS: argue ¬CurveIntegrable RHS form γ_Y by bounding through ψ Lipschitz.
  ...
case pos =>
  -- Apply Lebesgue: integrable + Bochner ⇒ AC ⇒ diff a.e.
  -- Use chain rule a.e.
  ...
```

This avoids API changes but requires:
* Symmetry: `CurveIntegrable LHS γ_X ↔ CurveIntegrable RHS γ_Y`.
* Lebesgue: integrable curveIntegralFun ⇒ AC ⇒ diff a.e.

The symmetry is plausible (ψ Lipschitz on compact range bounds RHS by LHS).
But the Lebesgue argument requires non-trivial Mathlib machinery
(Bochner integration, AC characterization).

### Effort estimate

**Total: ~300+ lines.** Most complex but avoids API change.

## Recommendation

**Implement Strategy A.** The Lipschitz hypothesis is the natural
regularity condition for path integration; the cascade through the API
is straightforward; and the sub-helpers (subpath Lipschitz, chartLift
Lipschitz) are useful elsewhere in the project.

The eventual `periodPairing` API would use either:
* Restrict to Lipschitz/smooth singular simplices (subcomplex of singular
  homology, quasi-isomorphic by smoothing arguments).
* Define an auxiliary `LipschitzPath` type and route through it.

For immediate progress, Strategy A on the chart-level lemma is the right
next step.

## Next-step action items

1. Create `Jacobian/Periods/PathLipschitz.lean` with:
   - `Path.subpath_lipschitzWith` (subpath preserves Lipschitz with adjusted constant).
   - `chartLift_lipschitzOn` (chart-lift of a Lipschitz path is Lipschitz on `Icc 0 1`).
2. Update `pathIntegralViaChartCorrect_pullbackFormsBundledLM`:
   - Add `(K : ℝ≥0) (hγ_Lip : LipschitzWith K γ.toFun)` to the signature.
   - Discharge the sorry using the Lipschitz bound + contradiction argument
     in the bad case.
3. Cascade through `pathIntegralViaCoverWith_pullback_via_common_partition`
   (uses `subpath_lipschitzWith`).
4. Continue cascading to `pathIntegralViaCoverWith_pullbackFormsBundledLM`,
   `pathIntegralViaCover_pullbackFormsBundledLM`, etc.
5. Higher-level: decide whether to require Lipschitz at the
   `IntegralOneCycle` level or use a "smooth representative" approach.
