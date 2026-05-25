import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectTrans
import Jacobian.Periods.ChartLiftTrans
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Path concatenation for the from-`X` corrected `pathIntegralViaChartCorrect`

Lifts the conditional in-chart `_trans` linearity to the from-`X`
layer using `chartLift_trans` (chart lift commutes with path
concatenation). Requires `CurveIntegrable` for both halves on the
chart-lifted subpaths.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Conditional path-concatenation linearity (from-`X`, corrected):
if the chart pullback of `ω` is curve-integrable along both
chart-lifted halves, the integral along `γab.trans γbd` distributes.
-/
theorem pathIntegralViaChartCorrect_trans_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b d : X} (γab : Path a b) (γbd : Path b d)
    (h : range (γab.trans γbd) ⊆ c.source)
    (hab : range γab ⊆ c.source) (hbd : range γbd ⊆ c.source)
    (h₁ : CurveIntegrable (chartedFormPullback c ω) (chartLift c γab hab))
    (h₂ : CurveIntegrable (chartedFormPullback c ω) (chartLift c γbd hbd)) :
    pathIntegralViaChartCorrect c ω (γab.trans γbd) h =
      pathIntegralViaChartCorrect c ω γab hab +
        pathIntegralViaChartCorrect c ω γbd hbd := by
  unfold pathIntegralViaChartCorrect
  rw [chartLift_trans c γab γbd h hab hbd]
  exact pathIntegralInChartCorrect_trans_of_curveIntegrable c ω _ _ h₁ h₂

end JacobianChallenge.Periods
