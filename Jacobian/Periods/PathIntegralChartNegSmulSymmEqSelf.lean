import Jacobian.Periods.PathIntegralChartLinear
import Jacobian.Periods.PathIntegralChartSmulSymm

/-!
# Negate-and-reverse on a scalar multiple equals the original (provisional in-chart)

Provisional in-chart analogue: `∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`.
Composes `_neg + _smul_symm + neg_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Triple-cancellation (provisional in-chart):
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`.
-/
theorem pathIntegralInChart_neg_smul_symm_eq_self
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (-(k • ω)) γ.symm =
      k • pathIntegralInChart c ω γ := by
  rw [pathIntegralInChart_neg, pathIntegralInChart_smul_symm, neg_neg]

end JacobianChallenge.Periods
