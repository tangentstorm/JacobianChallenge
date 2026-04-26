import Jacobian.Periods.PathIntegralChartCorrectLinear
import Jacobian.Periods.PathIntegralChartCorrectSimp

/-!
# In-chart `_neg`/`_symm` corollary

In-chart corrected analogue of `PathIntegralViaCoverNegSymm`:
integrating `-ω` along a chart-coordinate path `γ : Path a b` (in `E`)
equals integrating `ω` along `γ.symm`. Both equal
`-pathIntegralInChartCorrect c ω γ`.

This is the foundational version; the from-`X` and multi-chart
versions follow.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation along `γ` equals form along `γ.symm`. -/
theorem pathIntegralInChartCorrect_neg_form_eq_symm_path
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-ω) γ =
      pathIntegralInChartCorrect c ω γ.symm := by
  rw [pathIntegralInChartCorrect_neg, pathIntegralInChartCorrect_symm]

end JacobianChallenge.Periods
