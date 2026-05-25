import Jacobian.Periods.PathIntegralViaCoverNeg
import Jacobian.Periods.PathIntegralViaCoverSymm

/-!
# Negation-of-form vs reversal-of-path identity

A useful corollary combining `pathIntegralViaCoverWith_neg` (the
form-negation identity) with `pathIntegralViaCoverWith_symm` (the
path-reversal identity): integrating `-ω` along `γ` equals
integrating `ω` along `γ.symm` (with the appropriately re-indexed
cover).

This is the discrete analogue of `∫ -ω on γ = ∫ ω on -γ` from
classical complex analysis.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form-negation along `γ` equals form along `γ.symm`. Both equal
`- pathIntegralViaCoverWith ω γ`.
-/
theorem pathIntegralViaCoverWith_neg_form_eq_symm_path
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-ω) γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) := by
  rw [pathIntegralViaCoverWith_neg, pathIntegralViaCoverWith_symm]

end JacobianChallenge.Periods
