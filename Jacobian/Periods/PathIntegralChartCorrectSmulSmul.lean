import Jacobian.Periods.PathIntegralChartCorrectSmul

/-!
# Iterated scalar multiplication composes (in-chart corrected)

`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)`. Composes `_smul` with
`smul_smul` to fold an iterated scalar multiplication into a
single product.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Iterated scalar multiplication composes:
`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)`.
-/
theorem pathIntegralInChartCorrect_smul_smul
    (c : OpenPartialHomeomorph X E) (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (k • (l • ω)) γ =
      (k * l) • pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_smul, pathIntegralInChartCorrect_smul, smul_smul]

end JacobianChallenge.Periods
