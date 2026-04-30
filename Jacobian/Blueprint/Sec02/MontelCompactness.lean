import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Archimedean

/-! # Blueprint stub: `lem:montel-compactness`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Montel compactness in sequential form: every sequence
`ω_n : ℕ → H⁰(X, Ω¹)` with `‖ω_n‖ ≤ 1` has a subsequence
`ω_{φ n}` converging in sup norm to some `ω∞ ∈ H⁰(X, Ω¹)` with
`‖ω∞‖ ≤ 1`.

The statement is in **sequential** form (the topological-compactness
form `IsCompact (Metric.closedBall …)` lives downstream as
`hone_unit_ball_compact`, since stating it requires picking a normed
structure on `H⁰(X, Ω¹)`).

## Proof structure (this file)

After the `holomorphicSupNorm := ⨆ x : X, ‖ω.1 x‖` upgrade, the proof
is split TOPDOWN into:

* `holomorphicSupNorm_nonneg` (sorry-free): the sup norm is `≥ 0`,
  immediate from `Real.iSup_nonneg`.
* `holomorphicSupNorm_le_of_pointwise` (sorry-free): if every fibre
  norm `‖(ω - μ).1 x‖` is bounded by `r ≥ 0`, then so is
  `holomorphicSupNorm X (ω - μ)`. Standard `Real.iSup_le` after
  unfolding the definition through `cotangentFiberNorm`.
* `montel_pointwise_extraction` (**TODO leaf**): the analytic core —
  given a sup-norm-bounded sequence of holomorphic 1-forms, extract a
  subsequence `φ` and a limit `ωlim` together with the **pointwise
  uniform** ε-N condition on `‖(ω (φ n) - ωlim).1 x‖`, plus the
  sup-norm bound on `ωlim`. This bundles the four genuinely-missing
  Mathlib pieces in one named leaf:
    - per-chart Cauchy first-derivative estimate for holomorphic
      sections (chart-pulled-back from `chart_coefficient_bound`);
    - Arzelà–Ascoli for chart-pulled-back holomorphic functions on a
      closed disc;
    - diagonal subsequence over a finite chart subcover;
    - Weierstrass uniform-limit-of-holomorphic glued back into a
      global holomorphic 1-form.
  Downstream workers can split this into per-step sub-leaves once the
  underlying Mathlib infrastructure (Cauchy API for sections,
  Arzelà–Ascoli for `OpenPartialHomeomorph`-domain functions,
  Weierstrass for manifold sections) lands.
* `montel_compactness` (sorry-free): combines the three above —
  the leaf gives the pointwise data, `holomorphicSupNorm_le_of_pointwise`
  promotes it to sup-norm ε-N, and `Metric.tendsto_atTop` packages
  ε-N as `Tendsto … atTop (𝓝 0)` via `holomorphicSupNorm_nonneg`.

Per the project's "no ABSENT tier" policy, the missing analytic
content is concentrated at one precisely-named leaf rather than
dropped on the floor.

NOTE FOR WORKERS: this lemma stops at the **sequential**
`Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim)) atTop (𝓝 0)`.
The downstream consumer `hone_unit_ball_compact` wants
`IsCompact (Metric.closedBall (0 : H) 1)` for a normed-space
realisation `H`. The conversion is **not** trivially this lemma —
it requires the metric-space bridge "sequential compactness ⇒
topological compactness on first-countable spaces" (Mathlib:
`UniformSpace.isCompact_iff_isSeqCompact`, or
`IsSeqCompact.isCompact` on a metric space). Whoever picks up
`hone_unit_ball_compact` (Node 5) is responsible for that bridge —
this lemma's contract is the sequential form only. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold Topology
open Filter JacobianChallenge.HolomorphicForms

/-- The sup norm `holomorphicSupNorm X ω = ⨆ x, ‖ω.1 x‖` is
nonnegative. -/
lemma holomorphicSupNorm_nonneg
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : HolomorphicOneForm ℂ X) :
    0 ≤ holomorphicSupNorm X ω := by
  unfold holomorphicSupNorm cotangentFiberNormAt cotangentFiberNorm
  exact Real.iSup_nonneg (fun _ => norm_nonneg _)

/-- If the fiber norm `‖ω.1 x‖` is bounded by `r ≥ 0` pointwise on
`X`, then so is the sup norm. Routine `Real.iSup_le` after unfolding
the definition through `cotangentFiberNormAt` and `cotangentFiberNorm`. -/
lemma holomorphicSupNorm_le_of_pointwise
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : HolomorphicOneForm ℂ X) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x, ‖ω.1 x‖ ≤ r) :
    holomorphicSupNorm X ω ≤ r := by
  unfold holomorphicSupNorm cotangentFiberNormAt cotangentFiberNorm
  exact Real.iSup_le h hr

/-- **TODO leaf**: analytic core of Montel compactness, stated in
**pointwise** form (so the sup-norm packaging is moved out into the
sorry-free main proof).

Given a sup-norm-bounded sequence of holomorphic 1-forms on a compact
complex 1-manifold, extract a strictly monotone `φ : ℕ → ℕ` and a
limit form `ωlim : HolomorphicOneForm ℂ X` such that
`holomorphicSupNorm X ωlim ≤ 1` and the pointwise fibre-norm
differences `‖(ω (φ n) - ωlim).1 x‖` satisfy a **uniform-in-x** ε-N
condition.

The full proof of this leaf is the 8-step
Cauchy-estimate → equicontinuity → Arzelà–Ascoli → diagonal →
Weierstrass-glue argument from
`tex/sections/02-holomorphic-forms-and-genus.tex` lines 187–222.
The four genuinely-missing Mathlib pieces are listed in the file
docstring above. Held as a single named leaf because each piece is
substantial and the underlying infrastructure (Cauchy API for
sections, Arzelà–Ascoli for `OpenPartialHomeomorph`-domain functions,
manifold-Weierstrass) is not yet in place. Downstream workers can
sub-split when they have the supporting Mathlib lemmas. -/
private theorem montel_pointwise_extraction
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ x : X,
          ‖(ω (φ n) - ωlim).1 x‖ ≤ ε := by
  sorry

/-- Montel compactness (sequential form): the closed unit ball of
`H⁰(X, Ω¹)` is sequentially compact in the sup-norm sense.

Sorry-free orchestration: extracts pointwise uniform convergence from
the named leaf `montel_pointwise_extraction`, promotes it to sup-norm
ε-N via `holomorphicSupNorm_le_of_pointwise`, and packages ε-N as
`Tendsto … atTop (𝓝 0)` via `Metric.tendsto_atTop` and
`holomorphicSupNorm_nonneg`. -/
theorem montel_compactness
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim))
          atTop (𝓝 0) := by
  obtain ⟨φ, hφ, ωlim, hbnd, hpt⟩ :=
    montel_pointwise_extraction X ω _h_bounded
  refine ⟨φ, hφ, ωlim, hbnd, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := hpt (ε / 2) hε2
  refine ⟨N, fun n hn => ?_⟩
  have h_pt : ∀ x, ‖(ω (φ n) - ωlim).1 x‖ ≤ ε / 2 := hN n hn
  have h_le : holomorphicSupNorm X (ω (φ n) - ωlim) ≤ ε / 2 :=
    holomorphicSupNorm_le_of_pointwise X _ (le_of_lt hε2) h_pt
  have h_nn : 0 ≤ holomorphicSupNorm X (ω (φ n) - ωlim) :=
    holomorphicSupNorm_nonneg X _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn]
  linarith

end JacobianChallenge.Blueprint
