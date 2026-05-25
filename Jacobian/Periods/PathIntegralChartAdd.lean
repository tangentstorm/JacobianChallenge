import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.ChartedFormSimp
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Conditional addition linearity of the provisional `pathIntegralInChart`

Mirrors `Jacobian/Periods/PathIntegralChartCorrectAdd.lean` at the
provisional layer. `curveIntegral_add` requires both 1-forms to be
`CurveIntegrable`, so this `_add` lemma carries the per-form
integrability hypothesis. Becomes unconditional once Packet F lands
at the provisional layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional addition linearity of the provisional
`pathIntegralInChart`: if both `chartedForm c ω` and `chartedForm c η`
are curve-integrable along `γ`, the chart-local path integral
distributes over addition.
-/
theorem pathIntegralInChart_add_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hω : CurveIntegrable (chartedForm c ω) γ)
    (hη : CurveIntegrable (chartedForm c η) γ) :
    pathIntegralInChart c (ω + η) γ =
      pathIntegralInChart c ω γ + pathIntegralInChart c η γ := by
  show curveIntegral (chartedForm c (ω + η)) γ =
       curveIntegral (chartedForm c ω) γ +
         curveIntegral (chartedForm c η) γ
  rw [chartedForm_add]
  exact curveIntegral_add hω hη

end JacobianChallenge.Periods
