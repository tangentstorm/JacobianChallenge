import Jacobian.Periods.PathIntegralViaChartLinear
import Jacobian.Periods.PathLiftSimp

/-!
# Provisional from-`X` `_neg`/`_symm` corollary

Provisional from-`X` analogue of `PathIntegralViaChartCorrectNegSymm`:
integrating `-ω` along `γ` equals integrating `ω` along `γ.symm`.
Uses the simpler `chartedForm` (which drops the `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation along `γ` equals form along `γ.symm`. -/
theorem pathIntegralViaChart_neg_form_eq_symm_path
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c (-ω) γ h =
      pathIntegralViaChart c ω γ.symm h' := by
  rw [pathIntegralViaChart_neg, pathIntegralViaChart_symm c ω γ h h']

end JacobianChallenge.Periods
