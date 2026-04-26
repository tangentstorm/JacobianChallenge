import Jacobian.Periods.PathIntegralViaChartCorrectNeg
import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Single-chart `_neg`/`_symm` corollary

Single-chart analogue of `PathIntegralViaCoverNegSymm`:
integrating `-ω` along `γ` equals integrating `ω` along `γ.symm`.
Both equal `-pathIntegralViaChartCorrect c ω γ h`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation along `γ` equals form along `γ.symm`. -/
theorem pathIntegralViaChartCorrect_neg_form_eq_symm_path
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c (-ω) γ h =
      pathIntegralViaChartCorrect c ω γ.symm h' := by
  rw [pathIntegralViaChartCorrect_neg, pathIntegralViaChartCorrect_symm c ω γ h h']

end JacobianChallenge.Periods
