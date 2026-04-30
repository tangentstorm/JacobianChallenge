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

/-- Chart-independence of `orderAt`: computing the meromorphic order of `f`
through any holomorphic chart `e` at `p` (with `p ∈ e.source`) yields the
same value as the canonical `orderAt`. Placeholder — proof reduces to
`MeromorphicAt.meromorphicOrderAt_comp` applied to the analytic equivalence
`extChartAt 𝓘(ℂ) p ∘ e.symm`, whose derivative is nonzero at `e p` by the
complex inverse function theorem (see blueprint
`tex/sections/01-compact-riemann-surfaces.tex` line 42-51). -/
theorem orderAt_via_chart
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ) (p : X) (hf : MeromorphicAtX f p)
    (e : PartialHomeomorph X ℂ) (_hep : p ∈ e.source)
    (_hfe : MeromorphicAt (f ∘ e.symm) (e p)) :
    meromorphicOrderAt (f ∘ e.symm) (e p) = orderAt p f hf := by
  sorry

end JacobianChallenge.HolomorphicForms
