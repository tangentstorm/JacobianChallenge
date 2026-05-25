import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartLinear

/-!
# Scalar negation absorbs path reversal (provisional in-chart)

Provisional in-chart analogue of
`pathIntegralInChartCorrect_smul_symm_eq_neg_smul`:
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`. Uses the simpler `chartedForm`
(which drops the `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Scalar negation absorbs path reversal (provisional in-chart):
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`.
-/
theorem pathIntegralInChart_smul_symm_eq_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (k • ω) γ.symm =
      pathIntegralInChart c ((-k) • ω) γ := by
  rw [pathIntegralInChart_smul, pathIntegralInChart_symm,
      pathIntegralInChart_smul, neg_smul, smul_neg]

end JacobianChallenge.Periods
