import Jacobian.Periods.PathIntegralChartLinear

/-!
# Identity-scalar normalization (provisional in-chart)

`∫(1 • ω, γ) = ∫(ω, γ)` at the provisional in-chart layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (provisional in-chart). -/
theorem pathIntegralInChart_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c ((1 : ℂ) • ω) γ =
      pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_smul, one_smul]

end JacobianChallenge.Periods
