import Jacobian.Periods.PathIntegralViaChartCorrectSmul

/-!
# Identity-scalar normalization (via-chart corrected)

`∫(1 • ω, γ) = ∫(ω, γ)` at the from-`X` corrected layer.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (via-chart corrected). -/
theorem pathIntegralViaChartCorrect_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c ((1 : ℂ) • ω) γ h =
      pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_smul, one_smul]

end JacobianChallenge.Periods
