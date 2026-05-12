import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Blueprint: `def:vanishing-order` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The order of vanishing of a meromorphic germ at a point of a complex
manifold. Reduces to the chart-local Laurent series order via Mathlib's
`meromorphicOrderAt`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Order of vanishing of a function at a point of a complex 1-manifold.

The blueprint statement (`def:vanishing-order`) defines this for a
meromorphic germ via the Laurent order of `f ∘ (extChartAt 𝓘(ℂ) p).symm`
at `extChartAt 𝓘(ℂ) p p`, with chart independence proved separately.

Delegates to the production-side
`JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt`, which
is defined exactly as the blueprint specifies and carries the chart
independence proof
(`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`).

Type: `WithTop ℤ` (the convention is `+∞` for the zero germ and
negative integers for poles). -/
noncomputable def vanishingOrder
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (p : X) (f : X → ℂ) : WithTop ℤ :=
  JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p f

end JacobianChallenge.Blueprint
