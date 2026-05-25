import Jacobian.Periods.PathIntegralViaChartCorrectNeg
import Jacobian.Periods.PathIntegralViaChartCorrectSmul

/-!
# Form negation as scalar multiplication by `-1` (via-chart corrected)

Lifts the in-chart corrected `_neg_eq_neg_one_smul` to the from-`X`
layer.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form negation equals `(-1) •` on the integral
(via-chart corrected).
-/
theorem pathIntegralViaChartCorrect_neg_eq_neg_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChartCorrect c (-ω) γ h =
      (-1 : ℂ) • pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_neg, neg_one_smul]

end JacobianChallenge.Periods
