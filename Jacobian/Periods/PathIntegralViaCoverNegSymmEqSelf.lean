import Jacobian.Periods.PathIntegralViaCoverSymm
import Jacobian.Periods.PathIntegralViaCoverNeg

/-!
# Negate-and-reverse equals self (multi-chart cover)

Cover-layer analogue of `pathIntegralViaChartCorrect_neg_symm_eq_self`:
integrating `-ω` along `γ.symm` (with the Fin.rev-re-indexed cover)
equals integrating `ω` along `γ` (with the original cover).

Proof: `_symm` then `_neg` then `neg_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse cancellation (cover layer):
`∫(-ω, γ.symm) = ∫(ω, γ)`. -/
theorem pathIntegralViaCoverWith_neg_symm_eq_self
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-ω) γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) =
      pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_symm (-ω) γ n hn pickChart hcov,
      pathIntegralViaCoverWith_neg, neg_neg]

end JacobianChallenge.Periods
