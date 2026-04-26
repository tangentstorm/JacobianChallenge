import Jacobian.Periods.PathIntegralChart
import Mathlib.Topology.Path

/-!
# Lifting a path-on-`X` through a chart for integration

Queue D scaffolding. Two definitions wrapping
`pathIntegralInChart`:

* `chartLift c γ h` — takes a `γ : Path (a b : X)` whose range is
  contained in `c.source`, and returns the chart-coordinate path
  `Path (c a) (c b)` in the model space `E`. Uses Mathlib's
  `Path.map'`, which already accepts `ContinuousOn f (range γ)` —
  so `c.continuousOn_toFun.mono h` is the only continuity input.

* `pathIntegralViaChart c ω γ h` — the from-`X` wrapper around
  `pathIntegralInChart`. Lifts the path through the chart and
  applies the chart-local integral.

This addresses the deferred wrapper noted in
`PathIntegralChart.lean`: Mathlib's `Path.map` requires global
continuity, but `Path.map'` accepts a chart-source-restricted one.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

/-- Lift a path that stays inside a chart's source to a path in
the model space. -/
noncomputable def chartLift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) :
    Path (c a) (c b) :=
  γ.map' (c.continuousOn_toFun.mono h)

/-- Path integral of a holomorphic 1-form along a path that lies
inside a single chart's source. Lifts the path through the chart
and integrates the transported 1-form via Mathlib's `curveIntegral`. -/
noncomputable def pathIntegralViaChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) : ℂ :=
  pathIntegralInChart c ω (chartLift c γ h)

/-- The from-`X` chart-local path integral is `0` for the zero form. -/
@[simp] theorem pathIntegralViaChart_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (0 : HolomorphicOneForm E X) γ h = 0 := by
  unfold pathIntegralViaChart
  exact pathIntegralInChart_zero _ _

end JacobianChallenge.Periods
