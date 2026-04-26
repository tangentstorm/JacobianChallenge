import Jacobian.Periods.PathIntegralChart

/-!
# Round-trip integral is zero (provisional in-chart)

Provisional in-chart analogue of `pathIntegralInChartCorrect_add_symm_self`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
`pathIntegralInChart c ω γ + pathIntegralInChart c ω γ.symm = 0`. Uses
the simpler `chartedForm` (which drops the `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Round-trip cancellation (provisional in-chart): the integral
of `ω` along `γ` plus the integral along `γ.symm` is zero. -/
theorem pathIntegralInChart_add_symm_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c ω γ +
        pathIntegralInChart c ω γ.symm = 0 := by
  rw [pathIntegralInChart_symm, add_neg_cancel]

end JacobianChallenge.Periods
