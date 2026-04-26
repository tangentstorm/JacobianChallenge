import Jacobian.Periods.PathIntegralViaCoverSmulSymm
import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Scalar negation absorbs path reversal (cover layer)

Cover-layer analogue of `pathIntegralViaChartCorrect_smul_symm_eq_neg_smul`:
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)` (with the Fin.rev-re-indexed
cover for `γ.symm`).

Proof composes `_smul_symm`, `_smul`, `neg_smul`, `smul_neg`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Scalar negation absorbs path reversal (cover layer). -/
theorem pathIntegralViaCoverWith_smul_symm_eq_neg_smul
    (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (k • ω) γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) =
      pathIntegralViaCoverWith ((-k) • ω) γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_smul_symm k ω γ n hn pickChart hcov,
      pathIntegralViaCoverWith_smul, neg_smul]

end JacobianChallenge.Periods
