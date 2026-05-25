import Jacobian.Periods.PathIntegralViaCoverSymm

/-!
Cover-layer analogue of `pathIntegralViaChartCorrect_add_symm_self`:
the integral of `ω` along `γ` plus the integral of `ω` along `γ.symm`
(with the appropriately re-indexed cover via `cover_symm_of_cover`)
is zero.

Geometrically a special case of Stokes for an out-and-back loop.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]


theorem pathIntegralViaCoverWith_add_symm_self
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov +
        pathIntegralViaCoverWith ω γ.symm n hn (pickChart ∘ Fin.rev)
          (cover_symm_of_cover γ n hn pickChart hcov) = 0 := by
  rw [pathIntegralViaCoverWith_symm ω γ n hn pickChart hcov]
  exact add_neg_cancel _

end JacobianChallenge.Periods
