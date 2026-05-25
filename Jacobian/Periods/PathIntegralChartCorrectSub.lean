import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.ChartedFormPullbackSub
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Conditional subtraction linearity of `pathIntegralInChartCorrect`

Mathlib's `curveIntegral_sub` requires both forms `CurveIntegrable`.
This file packages it for our `chartedFormPullback` setup, parallel
to the `_add` lemma in `PathIntegralChartCorrectAdd.lean`. Becomes
unconditional once Packet F lands.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional subtraction linearity of `pathIntegralInChartCorrect`:
if both `chartedFormPullback c ω` and `chartedFormPullback c η` are
curve-integrable along `γ`, the chart-local path integral
distributes over subtraction.
-/
theorem pathIntegralInChartCorrect_sub_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hω : CurveIntegrable (chartedFormPullback c ω) γ)
    (hη : CurveIntegrable (chartedFormPullback c η) γ) :
    pathIntegralInChartCorrect c (ω - η) γ =
      pathIntegralInChartCorrect c ω γ - pathIntegralInChartCorrect c η γ := by
  show curveIntegral (chartedFormPullback c (ω - η)) γ =
       curveIntegral (chartedFormPullback c ω) γ -
         curveIntegral (chartedFormPullback c η) γ
  rw [chartedFormPullback_sub]
  exact curveIntegral_sub hω hη

end JacobianChallenge.Periods
