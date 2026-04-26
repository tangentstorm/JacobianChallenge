import Jacobian.Periods.PathIntegralChartCorrectSmul
import Jacobian.Periods.PathIntegralChartCorrectLinear

/-!
# In-chart corrected: form-negation factors through scalar negation

`∫(-(k • ω), γ) = (-k) • ∫(ω, γ)`. Composes `_neg` + `_smul` +
`neg_smul`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form-negation of a scalar multiple equals the negated scalar
multiple of the integral (in-chart corrected). -/
theorem pathIntegralInChartCorrect_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-(k • ω)) γ =
      (-k) • pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_neg, pathIntegralInChartCorrect_smul, ← neg_smul]

end JacobianChallenge.Periods
