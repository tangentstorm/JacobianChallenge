import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

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

Type: `WithTop ℤ` (the convention is `+∞` for the zero germ and
negative integers for poles). -/
noncomputable def vanishingOrder
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_p : X) (_f : X → ℂ) : WithTop ℤ :=
  sorry

end JacobianChallenge.Blueprint
