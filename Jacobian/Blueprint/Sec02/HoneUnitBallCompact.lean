import Jacobian.Blueprint.Sec02.MontelCompactness
import Mathlib.Analysis.Normed.Module.Basic

/-! # Blueprint stub: `thm:hone-unit-ball-compact`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The closed unit ball of `(H⁰(X, Ω¹), ‖·‖)` is compact (topological
form). This is the consumer that feeds Riesz's theorem
(`thm:fd-from-riesz`).

Because `HolomorphicOneForm ℂ X` carries no canonical normed-space
instance in Mathlib, the statement is parameterised by an *abstract*
normed `ℂ`-vector space `H` together with a `ℂ`-linear bijection
`HolomorphicOneForm ℂ X ≃ₗ[ℂ] H` whose norm matches
`holomorphicSupNorm`. The conclusion is `IsCompact (Metric.closedBall
(0 : H) 1)`, which is the precise precondition of
`FiniteDimensional.of_isCompact_closedBall`.

The downstream worker should prove this as: take a sequence in the
closed ball, push it through `e.symm` to a sequence of holomorphic
1-forms with sup norm `≤ 1`, apply `montel_compactness` to extract a
sup-norm convergent subsequence, push the limit back through `e` to
exhibit the metric-convergent subsequence. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Topological compactness of the closed unit ball of `H⁰(X, Ω¹)`,
parameterised by a normed-space realisation `H` of the section space
whose norm equals `holomorphicSupNorm`. -/
theorem hone_unit_ball_compact
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : HolomorphicOneForm ℂ X ≃ₗ[ℂ] H)
    (_h_norm : ∀ ω : HolomorphicOneForm ℂ X, ‖e ω‖ = holomorphicSupNorm X ω) :
    IsCompact (Metric.closedBall (0 : H) 1) := by
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
