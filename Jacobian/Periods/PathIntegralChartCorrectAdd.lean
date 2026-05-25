import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.ChartedFormPullbackSimp
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Conditional addition linearity of `pathIntegralInChartCorrect`

Mathlib's `curveIntegral_add` requires both 1-forms to be
`CurveIntegrable`. We package this for our `chartedFormPullback`
setup so future consumers can add path integrals as soon as both
forms are integrable along the path. The unconditional version is
gated on Packet F (`chartedFormPullback_curveIntegrable`).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional addition linearity of `pathIntegralInChartCorrect`:
if both `chartedFormPullback c ω` and `chartedFormPullback c η` are
curve-integrable along `γ`, the chart-local path integral
distributes over addition.
-/
theorem pathIntegralInChartCorrect_add_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hω : CurveIntegrable (chartedFormPullback c ω) γ)
    (hη : CurveIntegrable (chartedFormPullback c η) γ) :
    pathIntegralInChartCorrect c (ω + η) γ =
      pathIntegralInChartCorrect c ω γ + pathIntegralInChartCorrect c η γ := by
  show curveIntegral (chartedFormPullback c (ω + η)) γ =
       curveIntegral (chartedFormPullback c ω) γ +
         curveIntegral (chartedFormPullback c η) γ
  rw [chartedFormPullback_add]
  exact curveIntegral_add hω hη

end JacobianChallenge.Periods
