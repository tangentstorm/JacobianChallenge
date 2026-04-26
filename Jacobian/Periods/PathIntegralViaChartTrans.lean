import Jacobian.Periods.PathLift
import Jacobian.Periods.PathIntegralChartTrans
import Jacobian.Periods.ChartLiftTrans
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Path concatenation for the provisional from-`X` `pathIntegralViaChart`

Provisional via-chart analogue of
`pathIntegralViaChartCorrect_trans_of_curveIntegrable`. Lifts the
conditional in-chart `_trans` linearity via `chartLift_trans`. Uses
the simpler `chartedForm` (no `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Conditional path-concatenation linearity (provisional from-`X`):
if `chartedForm c ω` is curve-integrable along both chart-lifted
halves, the integral along `γab.trans γbd` distributes. -/
theorem pathIntegralViaChart_trans_of_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b d : X} (γab : Path a b) (γbd : Path b d)
    (h : range (γab.trans γbd) ⊆ c.source)
    (hab : range γab ⊆ c.source) (hbd : range γbd ⊆ c.source)
    (h₁ : CurveIntegrable (chartedForm c ω) (chartLift c γab hab))
    (h₂ : CurveIntegrable (chartedForm c ω) (chartLift c γbd hbd)) :
    pathIntegralViaChart c ω (γab.trans γbd) h =
      pathIntegralViaChart c ω γab hab +
        pathIntegralViaChart c ω γbd hbd := by
  sorry

end JacobianChallenge.Periods
