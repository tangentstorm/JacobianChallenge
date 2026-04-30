import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Mathlib.Topology.MetricSpace.Basic

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

Proof outline (downstream worker):
1. Cover `X` by finitely many charts; on each chart pull back `ω_n`
   to a holomorphic function `f_n : ℂ → ℂ` with sup bound `M`
   coming from `chart_coefficient_bound`.
2. Cauchy estimates ⇒ `|f_n'(z)| ≤ M / (R - r)` on a smaller disc,
   so the family `{f_n}` is equicontinuous on the smaller disc.
3. Arzelà–Ascoli on each chart extracts a uniformly convergent
   subsequence; diagonalise across the finite atlas.
4. Weierstrass: the uniform limit of holomorphic functions is
   holomorphic, so the limit lies in `H⁰(X, Ω¹)`.
5. Sup norm passes to the limit. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold Topology
open Filter JacobianChallenge.HolomorphicForms

/-- Montel compactness (sequential form): the closed unit ball of
`H⁰(X, Ω¹)` is sequentially compact in the sup-norm sense. -/
theorem montel_compactness
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → HolomorphicOneForm ℂ X)
    (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ ωlim : HolomorphicOneForm ℂ X,
        holomorphicSupNorm X ωlim ≤ 1 ∧
        Tendsto (fun n => holomorphicSupNorm X (ω (φ n) - ωlim))
          atTop (𝓝 0) := by
  /- PROOF SKETCH:
  1. Reduce to local charts and use the corresponding complex-analytic statement
     (isolated zeros/poles, local Laurent expansion, Cauchy estimate, Montel, or
     Riesz representation depending on the node).
  2. Transfer the local analytic estimate/property back through chart-change
     compatibility lemmas from the manifold API.
  3. Conclude the global statement by compactness/finite-subcover and standard
     linear-topological packaging in mathlib (Submodule, FiniteDimensional,
     CompactSpace, Proper, etc.).
  4. This theorem is intentionally left as a named blueprint leaf to be replaced
     by the concrete mathlib-facing implementation once supporting APIs land.
  -/
  sorry

end JacobianChallenge.Blueprint
