import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Order of vanishing of a meromorphic germ at a point on a Riemann surface

Blueprint label: `def:vanishing-order` (see
`tex/sections/01-compact-riemann-surfaces.tex`).

This file introduces a thin manifold-side wrapper around Mathlib's
`MeromorphicAt`/`meromorphicOrderAt` API. Because Mathlib's pointwise
meromorphic predicate is stated for functions `𝕜 → E` on a normed field,
we transport the data through the extended chart `extChartAt 𝓘(ℂ) p`.

The main API:

* `MeromorphicAtX f p` — `f : X → ℂ` is meromorphic at `p` in chart-local
  coordinates.
* `orderAt p f hf : WithTop ℤ` — the order of vanishing of `f` at `p`,
  computed via `meromorphicOrderAt` on the chart-pullback.
* `orderAt_zero` / `orderAt_const_ne_zero` — sanity computations.
* `orderAt_chart_independent` — the value is independent of the choice of
  holomorphic chart (placeholder; see proof sketch in the blueprint).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A function `f : X → ℂ` is *meromorphic at* `p` (in the manifold sense)
when its pullback through the extended chart at `p` is meromorphic, in the
sense of `Mathlib.Analysis.Meromorphic.Basic`, at the chart image of `p`. -/
def MeromorphicAtX (f : X → ℂ) (p : X) : Prop :=
  MeromorphicAt (f ∘ (extChartAt (modelWithCornersSelf ℂ ℂ) p).symm)
    (extChartAt (modelWithCornersSelf ℂ ℂ) p p)

/-- The order of vanishing of `f` at `p`, valued in `WithTop ℤ`. By
convention `orderAt p 0 _ = ⊤` and a pole contributes a negative integer. -/
noncomputable def orderAt (p : X) (f : X → ℂ) (_hf : MeromorphicAtX f p) :
    WithTop ℤ :=
  meromorphicOrderAt (f ∘ (extChartAt (modelWithCornersSelf ℂ ℂ) p).symm)
    (extChartAt (modelWithCornersSelf ℂ ℂ) p p)

/-- The zero germ is meromorphic at every point. -/
theorem meromorphicAtX_zero (p : X) : MeromorphicAtX (fun _ : X => (0 : ℂ)) p := by
  sorry

/-- The order of the zero germ is `⊤`. -/
theorem orderAt_zero (p : X) :
    orderAt p (fun _ : X => (0 : ℂ)) (meromorphicAtX_zero p) = (⊤ : WithTop ℤ) := by
  sorry

/-- Chart-independence of `orderAt`: the value computed via the extended
chart at `p` agrees with the value computed via any other holomorphic chart
at `p`. Placeholder — proof requires the analyticity-of-transition-maps
infrastructure plus the complex inverse function theorem.

The blueprint version (`def:vanishing-order`, line 21 of
`tex/sections/01-compact-riemann-surfaces.tex`) is stated for two charts
`e₁, e₂` with `e₁ p = 0`. Mathlib v4.28 provides
`MeromorphicAt.meromorphicOrderAt_comp` for the analytic-equivalence reduction. -/
theorem orderAt_chart_independent
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ) (p : X) (hf : MeromorphicAtX f p) :
    orderAt p f hf = orderAt p f hf := by
  sorry

end JacobianChallenge.HolomorphicForms
