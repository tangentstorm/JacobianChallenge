import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartLinear

/-!
# Provisional in-chart: form-negation factors through scalar negation

Provisional in-chart analogue of `pathIntegralInChartCorrect_neg_smul`:
`∫(-(k • ω), γ) = (-k) • ∫(ω, γ)`. Uses the simpler `chartedForm`
(no `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form-negation of a scalar multiple equals the negated scalar
multiple of the integral (provisional in-chart).
-/
theorem pathIntegralInChart_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-(k • ω)) γ =
      (-k) • pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_neg, pathIntegralInChart_smul, ← neg_smul]

end JacobianChallenge.Periods
