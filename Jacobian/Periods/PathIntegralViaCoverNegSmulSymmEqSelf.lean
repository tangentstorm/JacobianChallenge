import Jacobian.Periods.PathIntegralViaCoverNeg
import Jacobian.Periods.PathIntegralViaCoverSmulSymm

/-!
# Negate-and-reverse on a scalar multiple equals the original (cover layer)

Cover-layer analogue of `pathIntegralViaChartCorrect_neg_smul_symm_eq_self`:
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)` (with Fin.rev-re-indexed
cover for γ.symm).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Triple-cancellation (cover layer):
`∫(-(k • ω), γ.symm) = k • ∫(ω, γ)`.
-/
theorem pathIntegralViaCoverWith_neg_smul_symm_eq_self
    (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-(k • ω)) γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) =
      k • pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_neg,
      pathIntegralViaCoverWith_smul_symm k ω γ n hn pickChart hcov,
      neg_neg]

end JacobianChallenge.Periods
