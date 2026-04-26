import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.ChartedFormPullbackSimp
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Linearity of `pathIntegralInChartCorrect`

Negation lemma. The addition lemma is intentionally omitted: Mathlib's
`curveIntegral_add` requires `CurveIntegrable f₁ γ` and
`CurveIntegrable f₂ γ` hypotheses, which themselves need
continuity/smoothness of `chartedFormPullback c ω` along `γ`. We will
land `_add` once the smoothness theorem for `chartedFormPullback`
(or for the curve restriction) is proven; tracked in
`PathIntegralViaCoverRecon.lean` as the missing integrability helper.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The corrected chart-local path integral negates with the form. -/
@[simp] theorem pathIntegralInChartCorrect_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-ω) γ = - pathIntegralInChartCorrect c ω γ := by
  show curveIntegral (chartedFormPullback c (-ω)) γ =
       - curveIntegral (chartedFormPullback c ω) γ
  rw [chartedFormPullback_neg, curveIntegral_neg]

end JacobianChallenge.Periods
