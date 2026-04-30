import Jacobian.Blueprint.Sec02.MontelCompactness

/-! Blueprint: `thm:hone-unit-ball-compact` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

The closed unit ball of `(H⁰(X, Ω¹), ‖·‖)` is compact. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The closed unit ball of `H⁰(X, Ω¹)` (under the sup norm) is compact. -/
theorem hone_unit_ball_compact
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IsCompact {ω : X → ℂ | holomorphicSupNorm X ω ≤ 1} := by
  sorry

end JacobianChallenge.Blueprint
