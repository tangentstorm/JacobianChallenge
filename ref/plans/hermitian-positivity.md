# Plan: `thm:hermitian-positivity`

Blueprint label: `thm:hermitian-positivity`
Lean handle: `JacobianChallenge.Blueprint.hermitian_positivity`
File: `Jacobian/Blueprint/Sec03/HermitianPositivity.lean`
Class: **DECOMPOSE** (currently `True := trivial` placeholder)

## 1. Mathematical statement

For a nonzero holomorphic 1-form `ω : HolomorphicOneForm ℂ X` on a
compact connected Riemann surface `X`,

```
i · ∫_X ω ∧ conj ω  >  0     (as a real number).
```

Locally, in a chart `(U, φ)` with `φ_* ω = h(z) dz`,

```
i · ω ∧ conj ω  =  2 · |h(z)|² · dx ∧ dy
```

(a *pointwise nonnegative* (1,1)-form, strictly positive wherever
`h ≠ 0`). The result is the integral of a continuous nonnegative
density on a compact connected manifold, with at least one point of
strict positivity (because `ω ≠ 0`).

## 2. Choice of route

Two textbook routes:

- **Direct local-positivity + manifold-integration route.** Define the
  global integral `∫_X iω∧ω̄` via a partition of unity subordinate to
  a finite atlas. Use pointwise nonnegativity of the local integrand
  and the existence of one chart with strictly positive integrand
  (where `h ≠ 0`) to conclude the integral is `> 0`.

- **Riemannian-volume / Hodge route.** Identify `iω∧ω̄` as a
  pointwise inner product `‖ω‖²` against the dualizing volume form
  of a chosen Kähler metric, then invoke positivity of the volume
  form's measure.

**This plan adopts the direct route.** Reasons:

1. The Hodge / Kähler route requires the Hodge `*` operator, which is
   not packaged in Mathlib v4.28.0 for Riemann surfaces.
2. The local computation `iω∧ω̄ = 2|h|² dx∧dy` is a direct one-line
   chart-pulled exterior algebra fact; the manifold globalisation is
   shared infrastructure with `thm:stokes-on-rs-with-boundary` (the
   `integrateTwoForm` leaf).
3. Strict positivity is a measure-theoretic fact: a continuous
   nonnegative function on a connected manifold, positive at one
   point, has a chart neighborhood of positive measure on which it is
   bounded below by a positive constant.

## 3. Mathlib v4.28.0 inventory

| prerequisite | status | path |
|---|---|---|
| Smooth manifolds + atlas | PRESENT | `Mathlib.Geometry.Manifold.IsManifold` |
| Partition of unity subordinate to an atlas | PRESENT | `Mathlib.Geometry.Manifold.PartitionOfUnity` |
| Lebesgue measure / area form on `ℝ²` | PRESENT | `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` |
| Wedge product `∧` on cotangent fibers (alternating bilinear) | PARTIAL | `Mathlib.LinearAlgebra.AlternatingMap` (algebraic) |
| Conjugation of holomorphic 1-forms | ABSENT (project-side construction needed) | — |
| Pointwise type-(1,1) decomposition of `ω∧conjω` | ABSENT | — |
| Integration of (1,1)-forms on a 2-manifold | ABSENT (= Stokes plan leaf 3, `integrateTwoForm`) | — |
| Pointwise positivity of `‖h‖²` for holomorphic `h ≠ 0` | PRESENT | `Mathlib.Analysis.Complex.Basic`, `‖z‖²` semantics |
| Continuity of chart-pulled integrand | PRESENT | `ContMDiff` ⇒ continuity, Mathlib's chart-continuity API |

## 4. Decomposition (7 sub-leaves)

Each leaf gets a stable Lean handle in
`Jacobian/Blueprint/Sec03/HermitianPositivity.lean`. Several share
infrastructure with `ref/plans/stokes-on-rs-with-boundary.md` —
those are flagged.

| # | Lean handle | Class | Sketch | Deps |
|---|---|---|---|---|
| 1 | `holomorphicOneForm_conj` | MEDIUM | Define the *anti-holomorphic* conjugate `conjForm ω : HolomorphicOneForm ℂ X` (or rather, an anti-holomorphic section of the conjugate cotangent bundle). Pointwise `(conj ω) p v = conj (ω p v)`. Smoothness inherits via `Complex.conj.continuous`. | `HolomorphicOneForm`, `Complex.conj` |
| 2 | `wedge_one_form_conj_local` | SHORT | In any chart with `ω = h(z) dz`, the pointwise wedge `i · ω ∧ conj ω` equals `2|h(z)|² · (dx ∧ dy)` as a (1,1)-form. Direct exterior-algebra computation: `dz ∧ d̄z = -2i · dx ∧ dy`. | leaf 1, alternating-form algebra |
| 3 | `wedge_one_form_conj_local_nonneg` | SHORT | The local integrand `2|h(z)|²` is pointwise `≥ 0`. From `‖h(z)‖² ≥ 0` (basic). | leaf 2 |
| 4 | `wedge_one_form_conj_local_strict_at_nonzero_h` | SHORT | At any chart point where `h(z) ≠ 0`, the local integrand `2|h(z)|² > 0`. From `‖z‖ > 0 ↔ z ≠ 0`. | leaf 2 |
| 5 | `integrateTwoForm` (shared with Stokes plan leaf 3) | HARD | Define `∫_X` of a continuous (or `ContMDiff`) (1,1)-form on a compact 2-manifold via partition of unity + chart-pullback to `ℝ²` Lebesgue integral. Same construction as `ref/plans/stokes-on-rs-with-boundary.md` leaf 3. | partition of unity, MeasureTheory.Lebesgue |
| 6 | `integrateTwoForm_nonneg_of_pointwise_nonneg` | MEDIUM | If a (1,1)-form is pointwise nonnegative in every chart of a partition-of-unity-compatible atlas, its `integrateTwoForm` is `≥ 0`. Sum of nonnegatives. | leaf 5, monotonicity of `MeasureTheory.integral` |
| 7 | `integrateTwoForm_strict_of_chart_strict` | MEDIUM | If additionally the form is strictly positive on a non-null subset of one chart, the integral is `> 0`. Standard measure-theoretic fact: a continuous nonneg function with a positive value on a compact-Hausdorff connected manifold has a positive-measure positivity set. | leaf 5, `Continuous.eventually_pos` + `MeasureTheory.integral_pos_of_aestronglyMeasurable` |
| 8 | `nonzero_holomorphic_form_has_nonzero_chart_value` | SHORT | A nonzero `HolomorphicOneForm` `ω` has at least one point `p` and chart `(U, φ)` at `p` with `φ_*ω = h dz, h(p) ≠ 0`. Direct from `ω ≠ 0` ⇒ ∃ p, ω p ≠ 0, plus `chartAt`-continuity. | `HolomorphicOneForm` definition |
| 9 | `hermitian_positivity` (umbrella) | SHORT | Combine 1–8: leaf 8 provides a point of strict chart-local positivity (leaf 4); leaves 3 + 6 give global nonneg; leaf 7 promotes to strict positive. | leaves 3, 4, 5, 6, 7, 8 |

## 5. Assembly order

1. Leaf 1 (define `conjForm`, the anti-holomorphic conjugate).
2. Leaves 2 + 3 + 4 (local `iω∧conjω` is `2|h|² dx∧dy`, nonneg, strict at `h≠0`).
3. Leaf 5 (define `integrateTwoForm` — shared with Stokes plan).
4. Leaves 6 + 7 (manifold-level monotonicity / strict positivity).
5. Leaf 8 (a nonzero form has a nonzero chart value).
6. Leaf 9 (assemble).

## 6. Hodge route — recorded for completeness

H1. Equip `X` with a smooth Hermitian metric `g` (Riemann surface ⇒
    Kähler, automatically). Mathlib: `Mathlib.Geometry.Manifold.Riemannian`.
H2. Identify `iω∧conjω = ‖ω‖²_g · vol_g` for the volume form `vol_g`.
H3. Integrate `‖ω‖²_g` against `vol_g`'s positive Radon-Nikodym
    density.

Skipped: Mathlib's Riemannian metric on a Riemann surface lacks the
explicit `‖·‖²_g`-vs-Kähler-volume identity; setting it up is its own
~500 LOC project, longer than the direct route above.

## 7. LOC estimate

- Leaf 1: ~80 LOC (anti-holomorphic conjugate construction).
- Leaves 2, 3, 4: ~100 LOC total (chart-local algebra).
- Leaf 5: ~400 LOC if built standalone here, but **shared** with
  Stokes plan leaf 3 — true marginal cost is `0` once Stokes leaf 3
  lands; the wrapper is `~30 LOC`.
- Leaves 6, 7: ~80 LOC each.
- Leaf 8: ~60 LOC.
- Leaf 9: ~30 LOC.

Total marginal (assuming Stokes leaf 3 is shared) ≈ 460 LOC.
Total standalone ≈ 830 LOC.

## 8. What is genuinely blocked

After leaf 5 (`integrateTwoForm`) lands — the Mathlib gap shared with
Stokes — every remaining hermitian-positivity leaf is straightforward
chart-local complex analysis. **No surface classification, no Stokes,
no de Rham theorem, no Hodge `*`** is required for this route.

## 9. Aristotle packet plan (per leaf)

| Leaf | Risk | Notes |
|------|------|-------|
| 1 | medium | `conjForm` may need a bit of `ContMDiff`-section gymnastics. |
| 2 | low | Direct algebraic identity in a single chart. |
| 3 | low | `‖z‖² ≥ 0`. |
| 4 | low | `‖z‖² > 0 ↔ z ≠ 0`. |
| 5 | high | Manifold integration of (1,1)-forms — the actual Mathlib gap. Best attacked together with Stokes plan leaf 3 by a multi-day worker session. |
| 6 | medium | Once leaf 5 exists: monotonicity of integral. |
| 7 | medium | Once leaf 5 exists: continuity-driven strict positivity. |
| 8 | low | `ω ≠ 0` unfold. |
| 9 | low | One-line assembly. |

Sequencing: leaves 1, 2, 3, 4, 8 can be submitted to Aristotle today
(they don't depend on leaf 5). Leaves 5, 6, 7, 9 wait on Stokes plan
leaf 3 to land first.
