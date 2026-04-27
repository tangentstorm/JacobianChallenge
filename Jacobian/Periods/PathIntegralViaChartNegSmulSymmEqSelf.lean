import Jacobian.Periods.PathIntegralViaChartLinear
import Jacobian.Periods.PathIntegralViaChartSmulSymm

/-!
# Negate-and-reverse on a scalar multiple equals the original (provisional via-chart)

Provisional via-chart analogue, completing the triple-cancellation
family across all five layers:
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Triple-cancellation (provisional via-chart):
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`. -/
theorem pathIntegralViaChart_neg_smul_symm_eq_self
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c (-(k • ω)) γ.symm h' =
      k • pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_neg,
      pathIntegralViaChart_smul_symm c k ω γ h h',
      neg_neg]

end JacobianChallenge.Periods
