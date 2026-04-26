import Jacobian.Periods.PathIntegralViaChartCorrectNeg
import Jacobian.Periods.PathIntegralViaChartCorrectSmul

/-!
# From-`X` corrected: form-negation factors through scalar negation

Lifts the in-chart corrected `_neg_smul` to the from-`X` layer:
`∫(-(k • ω), γ) = (-k) • ∫(ω, γ)`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation of a scalar multiple equals the negated scalar
multiple of the integral (from-`X` corrected). -/
theorem pathIntegralViaChartCorrect_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (-(k • ω)) γ h =
      (-k) • pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_neg, pathIntegralViaChartCorrect_smul, ← neg_smul]

end JacobianChallenge.Periods
