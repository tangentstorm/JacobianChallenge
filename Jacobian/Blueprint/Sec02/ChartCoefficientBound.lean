import Jacobian.Blueprint.Sec02.HolomorphicSupNorm

/-! # Blueprint stub: `lem:chart-coefficient-bound`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Local coefficient bound on a chart `e : OpenPartialHomeomorph X ℂ` in
the atlas: there is a chart-local constant `C ≥ 0` such that for every
holomorphic 1-form `ω` and every `x ∈ e.source`, the fiber norm
`‖ω x‖_x` is bounded by `C * ‖ω‖`. The constant `C` depends only on the
chart and the partition-of-unity weight, not on `ω`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Chart-local fiber-norm bound: for each chart `e` in the atlas of
`X`, there is a constant `C ≥ 0` such that the fiber norm of any
holomorphic 1-form on `e.source` is bounded by `C` times the global
sup norm. -/
theorem chart_coefficient_bound
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : HolomorphicOneForm ℂ X) (x : X),
      x ∈ e.source →
        cotangentFiberNormAt X x (ω.1 x) ≤ C * holomorphicSupNorm X ω := by
  sorry

end JacobianChallenge.Blueprint
