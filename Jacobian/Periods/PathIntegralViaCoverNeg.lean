import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaChartCorrectNeg

/-!
# `pathIntegralViaCoverWith` negates with the form

The integral of `−ω` equals `−` the integral of `ω` on every segment,
so the multi-chart sum negates by distributing through `Finset.sum`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The multi-chart path integral negates with the form. -/
@[simp] theorem pathIntegralViaCoverWith_neg
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-ω) γ n hn pickChart hcov =
      - pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  unfold pathIntegralViaCoverWith
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact pathIntegralViaChartCorrect_neg _ _ _ _

end JacobianChallenge.Periods
