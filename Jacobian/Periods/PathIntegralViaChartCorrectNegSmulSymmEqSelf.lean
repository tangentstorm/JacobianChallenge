import Jacobian.Periods.PathIntegralViaChartCorrectNeg
import Jacobian.Periods.PathIntegralViaChartCorrectSmulSymm

/-!
# Negate-and-reverse on a scalar multiple equals the original (corrected via-chart)

`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`: combining form-negation,
scalar-multiplication, and path-reversal absorbs all three sign
flips. Composes `_neg + _smul_symm + neg_neg`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse on a scalar multiple cancels back to the
original `k • ∫(ω, γ)` (via-chart corrected). -/
theorem pathIntegralViaChartCorrect_neg_smul_symm_eq_self
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c (-(k • ω)) γ.symm h' =
      k • pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_neg,
      pathIntegralViaChartCorrect_smul_symm c k ω γ h h',
      neg_neg]

end JacobianChallenge.Periods
