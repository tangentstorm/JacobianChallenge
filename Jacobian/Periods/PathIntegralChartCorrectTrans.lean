import Jacobian.Periods.PathIntegralChartCorrect
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Path concatenation for `pathIntegralInChartCorrect`

Conditional `_trans` lemma: integrating along `γab.trans γbd` equals
the sum of integrating along `γab` and `γbd`. Requires
`CurveIntegrable` for both halves (parallel to the `_add` situation).

Becomes unconditional once Packet F lands the curve-integrability
of `chartedFormPullback c ω` for sufficiently smooth paths.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional path-concatenation linearity (in-chart corrected):
if the chart pullback of `ω` is curve-integrable along both `γab` and
`γbd`, the integral along `γab.trans γbd` distributes over the
concatenation point.
-/
theorem pathIntegralInChartCorrect_trans_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b d : E} (γab : Path a b) (γbd : Path b d)
    (h₁ : CurveIntegrable (chartedFormPullback c ω) γab)
    (h₂ : CurveIntegrable (chartedFormPullback c ω) γbd) :
    pathIntegralInChartCorrect c ω (γab.trans γbd) =
      pathIntegralInChartCorrect c ω γab +
        pathIntegralInChartCorrect c ω γbd := by
  show curveIntegral (chartedFormPullback c ω) (γab.trans γbd) =
       curveIntegral (chartedFormPullback c ω) γab +
         curveIntegral (chartedFormPullback c ω) γbd
  exact curveIntegral_trans h₁ h₂

end JacobianChallenge.Periods
