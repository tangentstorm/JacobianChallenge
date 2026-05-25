import Jacobian.Periods.PathIntegralChart
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Path concatenation for the provisional `pathIntegralInChart`

Conditional `_trans` lemma at the provisional in-chart layer:
integrating along `γab.trans γbd` equals the sum of integrating
along `γab` and `γbd`. Requires `CurveIntegrable` for both halves
(parallel to `_add`). Uses the simpler `chartedForm` (which drops
the `mfderiv` factor — fine for translation-transition charts).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional path-concatenation linearity (provisional in-chart):
if `chartedForm c ω` is curve-integrable along both `γab` and
`γbd`, the integral along `γab.trans γbd` distributes.
-/
theorem pathIntegralInChart_trans_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b d : E} (γab : Path a b) (γbd : Path b d)
    (h₁ : CurveIntegrable (chartedForm c ω) γab)
    (h₂ : CurveIntegrable (chartedForm c ω) γbd) :
    pathIntegralInChart c ω (γab.trans γbd) =
      pathIntegralInChart c ω γab +
        pathIntegralInChart c ω γbd := by
  show curveIntegral (chartedForm c ω) (γab.trans γbd) =
       curveIntegral (chartedForm c ω) γab +
         curveIntegral (chartedForm c ω) γbd
  exact curveIntegral_trans h₁ h₂

end JacobianChallenge.Periods
