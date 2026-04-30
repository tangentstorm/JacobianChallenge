import Jacobian.Blueprint.Sec02.HolomorphicSupNorm

/-! Blueprint: `lem:chart-coefficient-bound` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

Local coefficient bound on a chart: if `ω = h(z) dz` on `φ(U) ⊂ ℂ`, then
`|h(z)|` is bounded above by a chart-dependent constant times `‖ω‖`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Stub: there exists a chart-local constant such that the coefficient
function is bounded by that constant times the sup norm of the form. -/
theorem chart_coefficient_bound
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : X → ℂ) :
    ∃ C : ℝ, ∀ x : X, ‖ω x‖ ≤ C * holomorphicSupNorm X ω := by
  sorry

end JacobianChallenge.Blueprint
