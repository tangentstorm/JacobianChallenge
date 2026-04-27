import Jacobian.Periods.PathIntegralViaChartLinear

/-!
# Identity-scalar normalization (provisional via-chart)

`∫(1 • ω, γ) = ∫(ω, γ)` at the from-`X` provisional layer,
completing the 5-layer tower for `_one_smul`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (provisional via-chart). -/
theorem pathIntegralViaChart_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c ((1 : ℂ) • ω) γ h =
      pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_smul, one_smul]

end JacobianChallenge.Periods
