import Jacobian.Periods.PathIntegralChartLinear
import Jacobian.Periods.PathIntegralChart

/-!
# Provisional in-chart `_neg`/`_symm` corollary

Provisional in-chart analogue of `PathIntegralChartCorrectNegSymm`:
integrating `-ω` along a chart-coordinate path `γ : Path a b` (in `E`)
equals integrating `ω` along `γ.symm`. Uses the simpler `chartedForm`
(which drops the `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation along `γ` equals form along `γ.symm`. -/
theorem pathIntegralInChart_neg_form_eq_symm_path
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-ω) γ = pathIntegralInChart c ω γ.symm := by
  rw [pathIntegralInChart_neg, pathIntegralInChart_symm]

end JacobianChallenge.Periods
