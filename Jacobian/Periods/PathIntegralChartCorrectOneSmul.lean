import Jacobian.Periods.PathIntegralChartCorrectSmul

/-!
# Identity-scalar normalization (in-chart corrected)

`∫(1 • ω, γ) = ∫(ω, γ)` at the in-chart corrected layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (in-chart corrected). -/
theorem pathIntegralInChartCorrect_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c ((1 : ℂ) • ω) γ =
      pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_smul, one_smul]

end JacobianChallenge.Periods
