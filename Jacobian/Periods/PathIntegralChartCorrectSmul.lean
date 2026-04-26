import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.ChartedFormPullbackSmul
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The corrected chart-local path integral is ℂ-linear in the form. -/
@[simp] theorem pathIntegralInChartCorrect_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (k • ω) γ = k • pathIntegralInChartCorrect c ω γ := by
  show curveIntegral (chartedFormPullback c (k • ω)) γ =
       k • curveIntegral (chartedFormPullback c ω) γ
  rw [chartedFormPullback_smul, curveIntegral_smul]

end JacobianChallenge.Periods
