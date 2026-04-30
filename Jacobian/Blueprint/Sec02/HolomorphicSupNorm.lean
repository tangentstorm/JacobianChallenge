import Jacobian.Blueprint.Sec02.CotangentFiberNorm

/-! Blueprint: `def:holomorphic-sup-norm` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

Sup norm on the space of global holomorphic 1-forms `H⁰(X, Ω¹)`, defined
as `‖ω‖ = sup_{x ∈ X} ‖ω_x‖_x`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The sup norm on holomorphic 1-forms on `X`. Stub: the function is
parameterised on a placeholder `X → ℂ` (intended as the chart-local
representation of a 1-form). -/
noncomputable def holomorphicSupNorm
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω : X → ℂ) : ℝ := sorry

end JacobianChallenge.Blueprint
