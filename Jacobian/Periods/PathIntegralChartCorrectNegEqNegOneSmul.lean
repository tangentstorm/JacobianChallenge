import Jacobian.Periods.PathIntegralChartCorrectSmul
import Jacobian.Periods.PathIntegralChartCorrectLinear

/-!
# Form negation as scalar multiplication by `-1` (in-chart corrected)

`∫(-ω, γ) = (-1) • ∫(ω, γ)`. Bridges the unary form-negation and
ℂ-scalar-mul views of the integral.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form negation equals `(-1) •` on the integral
(in-chart corrected).
-/
theorem pathIntegralInChartCorrect_neg_eq_neg_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (-ω) γ =
      (-1 : ℂ) • pathIntegralInChartCorrect c ω γ := by
  rw [pathIntegralInChartCorrect_neg, neg_one_smul]

end JacobianChallenge.Periods
