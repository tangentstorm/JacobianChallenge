import Jacobian.Periods.PathIntegralViaChartCorrectSmul

/-!
# Iterated scalar multiplication composes (via-chart corrected)

`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)`. Composes `_smul` twice
+ `smul_smul`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Iterated scalar multiplication composes (via-chart corrected). -/
theorem pathIntegralViaChartCorrect_smul_smul
    (c : OpenPartialHomeomorph X E) (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (k • (l • ω)) γ h =
      (k * l) • pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_smul, pathIntegralViaChartCorrect_smul, smul_smul]

end JacobianChallenge.Periods
