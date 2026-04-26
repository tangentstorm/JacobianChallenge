import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.ChartedFormSmul
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Negation and scalar linearity of `pathIntegralInChart`

The in-chart version of `pathIntegralViaChartLinear`, completing the
provisional in-chart `_neg/_smul` ladder. (The corresponding `_zero`
already lives in `PathIntegralChart.lean`.)

Mirrors the corrected layer's `PathIntegralChartCorrectLinear` and
`PathIntegralChartCorrectSmul`. Addition is intentionally omitted:
`curveIntegral_add` requires `CurveIntegrable` for both summands.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The provisional chart-local path integral negates with the form. -/
@[simp] theorem pathIntegralInChart_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-ω) γ = - pathIntegralInChart c ω γ := by
  show curveIntegral (chartedForm c (-ω)) γ =
       - curveIntegral (chartedForm c ω) γ
  rw [chartedForm_neg, curveIntegral_neg]

/-- The provisional chart-local path integral is ℂ-linear in the form. -/
@[simp] theorem pathIntegralInChart_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (k • ω) γ = k • pathIntegralInChart c ω γ := by
  show curveIntegral (chartedForm c (k • ω)) γ =
       k • curveIntegral (chartedForm c ω) γ
  rw [chartedForm_smul, curveIntegral_smul]

end JacobianChallenge.Periods
