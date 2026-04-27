import Jacobian.Periods.PathIntegralViaCoverNeg
import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Form negation as scalar multiplication by `-1` (cover layer)

`pathIntegralViaCoverWith (-ω) γ ... = (-1) • pathIntegralViaCoverWith ω γ ...`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Form negation equals `(-1) •` on the integral (cover layer). -/
theorem pathIntegralViaCoverWith_neg_eq_neg_one_smul
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-ω) γ n hn pickChart hcov =
      (-1 : ℂ) • pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_neg, neg_one_smul]

end JacobianChallenge.Periods
