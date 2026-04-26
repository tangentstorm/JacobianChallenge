import Jacobian.Periods.PathIntegralViaChartLinear
import Jacobian.Periods.PathLiftSimp

/-!
# Negate-and-reverse equals self (provisional via-chart)

Provisional from-`X` analogue of `pathIntegralViaChartCorrect_neg_symm_eq_self`:
in a single chart `c` whose source contains both `γ` and `γ.symm`,
`pathIntegralViaChart c (-ω) γ.symm = pathIntegralViaChart c ω γ`.

Uses the simpler `chartedForm` (which drops the `mfderiv` factor).
Completes the negate-and-reverse cancellation family across all five
layers.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse cancellation (provisional via-chart):
`∫(-ω, γ.symm) = ∫(ω, γ)`. -/
theorem pathIntegralViaChart_neg_symm_eq_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c (-ω) γ.symm h' =
      pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_symm c (-ω) γ h h',
      pathIntegralViaChart_neg, neg_neg]

end JacobianChallenge.Periods
