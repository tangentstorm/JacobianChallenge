import Jacobian.Periods.PathIntegralChartCorrectLinear
import Jacobian.Periods.PathIntegralChartCorrectSmulSymm

/-!
# Negate-and-reverse on a scalar multiple equals the original (in-chart corrected)

In-chart corrected analogue of `pathIntegralViaChartCorrect_neg_smul_symm_eq_self`:
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`. Composes `_neg + _smul_symm + neg_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Triple-cancellation (in-chart corrected):
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`. -/
theorem pathIntegralInChartCorrect_neg_smul_symm_eq_self
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-(k • ω)) γ.symm =
      k • pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_neg, pathIntegralInChartCorrect_smul_symm,
      neg_neg]

end JacobianChallenge.Periods
