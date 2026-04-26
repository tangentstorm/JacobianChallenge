import Jacobian.Periods.PathIntegralViaCoverSmul
import Jacobian.Periods.PathIntegralViaCoverSymm

/-!
# Scalar-multiplication along reversed path

Combining `pathIntegralViaCoverWith_smul` (form-side scalar
multiplication) with `pathIntegralViaCoverWith_symm` (path-reversal):
integrating `k • ω` along `γ.symm` (with the appropriately re-indexed
cover) equals `-(k • pathIntegralViaCoverWith ω γ)`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Scalar-multiplication along the reversed path: `k • ω` along
γ.symm equals minus `k • (cover-with integral of ω along γ)`. -/
theorem pathIntegralViaCoverWith_smul_symm
    (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (k • ω) γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) =
      -(k • pathIntegralViaCoverWith ω γ n hn pickChart hcov) := by
  rw [pathIntegralViaCoverWith_smul, pathIntegralViaCoverWith_symm, smul_neg]

end JacobianChallenge.Periods
