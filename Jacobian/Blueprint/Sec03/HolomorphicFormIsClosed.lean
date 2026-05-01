import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! Blueprint stub: `lem:holomorphic-form-is-closed` in
`tex/sections/03-periods-and-riemann-bilinear.tex`.

A holomorphic 1-form `ω` on a complex 1-manifold is closed: `dω = 0`,
equivalently the exterior derivative vanishes pointwise on `X`.

## Status

**Stub-with-True placeholder.** Mathlib v4.28.0 (the pinned commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`) does not expose a clean
exterior-derivative API for differential forms on charted spaces;
`Mathlib.Geometry.Manifold.MFDeriv.Basic` gives `mfderiv` for first
derivatives of maps, but `HolomorphicOneForm² ℂ X` (the codomain of
the would-be `d`) is not defined.

The real conclusion is `dω = 0` for the exterior derivative `d`. Until
the manifold-side exterior-derivative API lands (or the project's
own `Jacobian/HolomorphicForms/` scaffolding adds one), the
declaration body is `True` so the blueprint dep-graph can pick up the
`\lean{…}` annotation. Downstream consumers
(`Jacobian/Blueprint/Sec03/PeriodHomologyInvarianceStatement.lean` and
`Stokes`-based lemmas) will be retargeted at the real conclusion when
the API is in.

## Proof sketch (for the eventual real conclusion)

Local computation in any chart: if `e : OpenPartialHomeomorph X ℂ` is
a chart at `p` with the chart-pulled-back representation
`ω = h(z) dz` for some `h : ℂ → ℂ` analytic at `e p`, then
`d(h(z) dz) = ∂h/∂z̄ · dz̄ ∧ dz = 0` by the Cauchy–Riemann equations
(`∂h/∂z̄ = 0` since `h` is holomorphic). Globalisation: chart-overlap
compatibility + linearity of `d` gives independence of chart, so the
chart-local vanishing assembles into the global `dω = 0`.

Mathlib decls expected to support the real proof when the API lands:
`MDifferentiable`, `mfderiv`, `Mathlib.Analysis.Calculus.FDeriv.Analytic`
(`AnalyticAt → DifferentiableAt`), and a manifold-side
`exteriorDerivative` once introduced. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Holomorphic 1-forms are closed. The exterior derivative `dω` of a
holomorphic 1-form `ω` vanishes — a direct consequence of the
Cauchy–Riemann equations in any chart, globalised via chart-overlap
compatibility.

Currently a `True` placeholder pending a manifold-side
exterior-derivative API in Mathlib (or a project-side definition of
`HolomorphicOneForm² ℂ X` so the conclusion `dω = 0` can be
type-checked here). See file docstring for the proof sketch and
`Mathlib` decl pointers. -/
theorem holomorphic_form_is_closed
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω : HolomorphicOneForm ℂ X) :
    True := by
  trivial

end JacobianChallenge.Blueprint
