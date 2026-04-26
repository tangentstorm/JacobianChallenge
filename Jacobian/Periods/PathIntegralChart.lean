import Jacobian.Periods.ChartedForm
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Path integral of a holomorphic 1-form in a single chart

Queue D scaffolding. Defines `pathIntegralInChart c ω γ`: the
integral of a `HolomorphicOneForm E X` along a path `γ` that has
already been transported into the model space `E` via a chart `c`.

The signature takes the *transported* path `γ : Path (a : E) (b : E)`
rather than a path on `X`, because Mathlib's `Path.map` needs a
globally-continuous map between topological spaces and our chart
`c.toFun` is only continuous on `c.source`. The from-`X` wrapper
will live in a follow-up file once the chart-source restriction
machinery is in place.

The integral itself is just Mathlib's `curveIntegral` applied to
`chartedForm c ω` (the chart-local transport of the 1-form to `E`).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/-- Path integral of a holomorphic 1-form, evaluated in chart
coordinates. The path `γ` is required to live in the model space
`E` (already transported through the chart `c`). -/
noncomputable def pathIntegralInChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X)
    {a b : E}
    (γ : Path a b) : ℂ :=
  curveIntegral (chartedForm c ω) γ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The chart-local path integral over a constant path is zero. -/
@[simp] theorem pathIntegralInChart_refl
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (a : E) :
    pathIntegralInChart c ω (Path.refl a) = 0 :=
  curveIntegral_refl _ a

/-- The chart-local path integral reverses sign under path symmetry. -/
theorem pathIntegralInChart_symm
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c ω γ.symm = - pathIntegralInChart c ω γ :=
  curveIntegral_symm _ γ

end JacobianChallenge.Periods
