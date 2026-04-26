import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaChartCorrectSmul

/-!
# `pathIntegralViaCoverWith` is ℂ-linear in the form (scalar multiplication)

The integral of `k • ω` equals `k •` the integral of `ω` on every segment,
so the multi-chart sum scales by distributing through `Finset.sum`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The multi-chart path integral is ℂ-linear in the form. -/
@[simp] theorem pathIntegralViaCoverWith_smul
    (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (k • ω) γ n hn pickChart hcov =
      k • pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  unfold pathIntegralViaCoverWith
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact pathIntegralViaChartCorrect_smul _ _ _ _ _

end JacobianChallenge.Periods
