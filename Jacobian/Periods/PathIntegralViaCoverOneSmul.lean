import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Identity-scalar normalization (cover layer)

`∫(1 • ω, γ) = ∫(ω, γ)` at the cover-with layer. Trivial via
`one_smul` or `_smul` + `one_smul`. Useful for normalizing
expressions where a stray `1 •` appears.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (cover layer). -/
theorem pathIntegralViaCoverWith_one_smul
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ((1 : ℂ) • ω) γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_smul, one_smul]

end JacobianChallenge.Periods
