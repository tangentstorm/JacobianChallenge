import Mathlib

/-!
# Recon: Chart-coefficient extraction for `ContMDiffSection` of cotangent bundles

This file documents the Mathlib v4.28.0 API gap that blocks the
Liouville-core leaves of the genus-zero classification:

* `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` and
* `holomorphicOneForm_onePointCx_toFun_infty_eq_zero`

in `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.  Two
Aristotle packets — `d493c66b` (138 min stuck at 37%) and `1f7d4399`
(31 min stuck at 20%) — both hit this gap.  This recon names what's
missing and proposes a project-local extraction lemma.

## What we have (in the project)

* `OnePoint.OnePointCxChartedSpace` instance — `ChartedSpace ℂ (OnePoint ℂ)`
  with two charts (identity, inversion).
* `OnePointCxIsManifold` — `IsManifold 𝓘(ℂ, ℂ) ⊤ (OnePoint ℂ)`.
* `HolomorphicOneForm ℂ (OnePoint ℂ)` is a `ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ⊤`
  of the cotangent bundle (a `Bundle.ContinuousLinearMap` bundle).
* `Jacobian/HolomorphicForms/EntireZero.lean` — 5 sorry-free Liouville-zero
  corollaries, including `Differentiable.eq_zero_of_tendsto_zero_cocompact`.

## What we need (the gap)

A way to read a `ContMDiffSection σ : ContMDiffSection I F ⊤ V` of a
vector bundle `V` over a chart domain as a function from the chart's
target space (in our case `ℂ`) into the model fiber `F` (in our case
`ℂ →L[ℂ] ℂ`), preserving:

1. `ContMDiff` ↦ `ContDiff` on the chart (so we can apply complex-analytic
   theorems like `Differentiable`/Liouville to the local representation);
2. The chart-transition formula linking the local representation in
   one chart to the local representation in another chart.

Specifically for the cotangent bundle on `OnePoint ℂ`:

```
identity chart (source `{∞}ᶜ ≅ ℂ`):
  ω.toFun (↑z) = f(z) · dz   for some f : ℂ → ℂ entire

inversion chart (source `{(↑0 : OnePoint ℂ)}ᶜ`, forward `↑z ↦ z⁻¹`,
                 `∞ ↦ 0`):
  ω.toFun (↑z) = g(z⁻¹) · dz  in chart coords
              = -f(z⁻¹) · z⁻² · dz  via chain rule on z ↦ z⁻¹
```

So for `ω` to be `ContMDiff` at `∞`, the function `g(w) = -f(1/w)/w²`
must extend `ContDiff` across `w = 0`.  This forces `f` to vanish at
infinity, which by Liouville (via `EntireZero.lean`) forces `f = 0`.

## Mathlib v4.28.0 status

What exists:

| API | Found? | Notes |
|---|---|---|
| `ContMDiffSection` | ✅ | Structure with `.toFun`, `.contMDiff_toFun`. |
| `ContMDiffSection.contMDiff_toFun` | ✅ | Smoothness as a section. |
| `ContMDiff` lifting through chart | ✅ (general) | `contMDiff_iff_chart` family. |
| `Trivialization.continuousAt_iff` | ✅ | For `IsManifold` of total space. |
| `VectorBundle` / `Trivialization` | ✅ | But ContinuousLinearEquiv only. |
| Cotangent bundle as `Bundle.ContinuousLinearMap` | ✅ (via Mathlib) | `TangentSpace 𝓘(ℂ,ℂ) x →L[ℂ] ℂ`. |
| Chart-transition for cotangent bundle | ❌ | Not user-facing. |
| `localCoeff` / `localRepr` for `ContMDiffSection` | ❌ | Project-local addition needed. |
| `NormedVectorBundle` class | ❌ | Surfaced by `63158306` for the fiber-norm continuity. |

## Proposal: project-local extraction lemma

The cleanest path forward is to add a project-local extraction
helper, e.g.:

```lean
/-- Local coefficient of a smooth section through a chart trivialisation.

Given a smooth section `σ` of a vector bundle `V` over a chart domain,
returns the corresponding function on the chart target — i.e., the
composition of the section with the local trivialisation, expressed
in chart coordinates. -/
noncomputable def ContMDiffSection.localCoeff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ⊤ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
    [VectorBundle 𝕜 F V]
    (σ : ContMDiffSection I F ⊤ V) (e : Trivialization F (π F V))
    (c : PartialHomeomorph M H) :
    H → F :=
  fun h => (e (TotalSpace.mk' F (c.symm h) (σ.toFun (c.symm h)))).2

theorem ContMDiffSection.localCoeff_contDiff
    (σ : ContMDiffSection I F ⊤ V) (e : Trivialization F (π F V))
    (c : PartialHomeomorph M H)
    (compat : <suitable compatibility hypotheses>) :
    ContDiff 𝕜 ⊤ (σ.localCoeff e c) := sorry
```

This would fold the chart + trivialisation composition into a single
named function with a smoothness proof, making the Liouville-core
arguments tractable.

## Concrete next steps

1. **Aristotle survey packet:** ask for a precise statement of
   `localCoeff` + smoothness, with the specific compatibility
   hypotheses required.  Acceptable outcomes: full proof, named
   sub-obligations, or detailed Mathlib-API-gap survey.
2. **For the cotangent-on-`OnePoint ℂ` case specifically:** the model
   fiber is `ℂ →L[ℂ] ℂ`, which is canonically `ℂ` via evaluation at
   `1 : ℂ`.  A specialised `holomorphicOneForm_localCoeff_onePointCx`
   in this concrete setting may be easier than the general bundle
   theorem and still suffice for the Liouville-core leaves.
3. **Chart-transition formula:** prove
   `ω.toFun (↑z)` reads as `f(z)` on the identity chart and as
   `-f(1/w)/w²` on the inversion chart at `w = z⁻¹`, by direct
   computation from the chart definitions in
   `Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean`.

## History of cancelled packets

| Job | Stuck at | Duration | Notes |
|---|---|---|---|
| `d493c66b` | 37% | 138 min | First TOPDOWN attempt on the chart-extraction. Cancelled, replaced by local split + 1f7d4399. |
| `1f7d4399` | 20% | 31 min | TOPDOWN on the now-narrower finite leaf. Made initial progress (1→20%), then complete flatline. Hypothesis: Aristotle hit the chart-extraction gap at the trivialisation-composition step. |

Both packets had the EntireZero.lean Liouville core available as a
black box; the bottleneck was the bundle-API extraction, not the
analytic content.
-/
