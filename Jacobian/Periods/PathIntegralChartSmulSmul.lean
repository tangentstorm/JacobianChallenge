import Jacobian.Periods.PathIntegralChartLinear

/-!
# Iterated scalar multiplication composes (provisional in-chart)

`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)` at the provisional in-chart
layer. Uses the simpler `chartedForm` (no `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Iterated scalar multiplication composes (provisional in-chart). -/
theorem pathIntegralInChart_smul_smul
    (c : OpenPartialHomeomorph X E) (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (k • (l • ω)) γ =
      (k * l) • pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_smul, pathIntegralInChart_smul, smul_smul]

end JacobianChallenge.Periods
