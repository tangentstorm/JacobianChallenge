import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Iterated scalar multiplication composes (cover layer)

`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)` at the cover-with layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Iterated scalar multiplication composes (cover layer). -/
theorem pathIntegralViaCoverWith_smul_smul
    (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (k • (l • ω)) γ n hn pickChart hcov =
      (k * l) • pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_smul, pathIntegralViaCoverWith_smul, smul_smul]

end JacobianChallenge.Periods
