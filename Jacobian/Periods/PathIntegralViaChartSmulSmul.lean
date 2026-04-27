import Jacobian.Periods.PathIntegralViaChartLinear

/-!
# Iterated scalar multiplication composes (provisional via-chart)

Provisional via-chart layer of `_smul_smul`, completing the family
across all five layers.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Iterated scalar multiplication composes (provisional via-chart). -/
theorem pathIntegralViaChart_smul_smul
    (c : OpenPartialHomeomorph X E) (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (k • (l • ω)) γ h =
      (k * l) • pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_smul, pathIntegralViaChart_smul, smul_smul]

end JacobianChallenge.Periods
