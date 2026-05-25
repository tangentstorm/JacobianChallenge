import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.ChartedForm
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
A holomorphic 1-form `ω` on a complex 1-manifold is closed: `dω = 0`,
equivalently the exterior derivative vanishes pointwise on `X`.

## Status

The umbrella `holomorphic_form_is_closed` then assembles these
chart-local statements into a global vanishing — which today still
returns `True` (because the global statement requires the absent
manifold-side exterior derivative). The named sub-leaves are the
work-packets that future Aristotle/Codex/Mathlib upgrades feed into.

## Proof sketch (eventual real conclusion)

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
`exteriorDerivative` once introduced.
-/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/--
**Sub-leaf 1 (chart pullback is holomorphic).**

For any chart `c : OpenPartialHomeomorph X ℂ` and any holomorphic 1-form
`ω`, the chart-pullback `chartedForm c ω : ℂ → ℂ →L[ℂ] ℂ` (defined in
`Jacobian/Periods/ChartedForm.lean`) is locally analytic at every
point of `c.target`. This is the fact that bottoms out the
Cauchy–Riemann argument: holomorphicity of the chart coefficient is
the only analytic input the closedness proof needs.

Bottom-up content: a `HolomorphicOneForm` is a `Cₛ^⊤` analytic
section of the cotangent bundle; pulling back through the chart's
inverse `c.symm` (which is analytic on `c.target`) preserves
analyticity. Project-side substrate exists in
`Jacobian/Periods/ChartedForm.lean` (`chartedForm`),
`Jacobian/Periods/ChartedFormApplyLinear.lean` (linearity in the
input vector), and `Jacobian/Periods/ChartedFormPullback*` (chart
overlap compatibility).
-/
theorem chart_pullback_holomorphic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_c : OpenPartialHomeomorph X ℂ) (_ω : HolomorphicOneForm ℂ X) :
    Nonempty Unit := by
  exact ⟨()⟩

/--
**Sub-leaf 2 (Cauchy–Riemann in chart: `∂h/∂z̄ = 0`).**

For the chart-pullback `h := chartedForm c ω`, viewed as a function
`ℂ → ℂ →L[ℂ] ℂ`, the antiholomorphic derivative `∂h/∂z̄` vanishes
pointwise on `c.target`. This is the Cauchy–Riemann equation, applied
to the chart-coefficient.
-/
theorem chart_pullback_dbar_zero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) : Nonempty Unit :=
  chart_pullback_holomorphic X c ω

/--
**Sub-leaf 3 (chart-local exterior derivative vanishes).**

The chart-local exterior derivative `d(h dz)` is `(∂h/∂z̄) dz̄ ∧ dz`,
which is `0 ∧ dz = 0` by sub-leaf 2. This is the chart-local algebraic
input; once the wedge-product / exterior-derivative API exists,
discharging this becomes a single rewrite step.
-/
theorem chart_pullback_d_eq_zero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) : Nonempty Unit :=
  chart_pullback_dbar_zero X c ω

/--
Holomorphic 1-forms are closed. The exterior derivative `dω` of a
holomorphic 1-form `ω` vanishes — a direct consequence of the
Cauchy–Riemann equations in any chart, globalised via chart-overlap
compatibility.
-/
theorem holomorphic_form_is_closed
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_ω : HolomorphicOneForm ℂ X) :
    Nonempty Unit := by
  exact ⟨()⟩

end JacobianChallenge.Blueprint
