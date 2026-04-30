import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Blueprint: `lem:montel-compactness` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

Montel compactness: the closed unit ball of `H⁰(X, Ω¹)` is sequentially
compact. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Sequential compactness of the unit ball of `H⁰(X, Ω¹)` under the sup
norm. The current statement is a placeholder asserting that every
bounded sequence has a uniform limit on `X`. -/
theorem montel_compactness
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ℕ → (X → ℂ)) (_h_bounded : ∀ n, holomorphicSupNorm X (ω n) ≤ 1) :
    ∃ (φ : ℕ → ℕ) (_hφ : StrictMono φ) (ωlim : X → ℂ),
      holomorphicSupNorm X ωlim ≤ 1 ∧
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖ω (φ n) x - ωlim x‖ ≤ ε := by
  sorry

end JacobianChallenge.Blueprint
