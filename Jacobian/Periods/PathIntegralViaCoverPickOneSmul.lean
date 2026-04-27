import Jacobian.Periods.PathIntegralViaCoverPickSmul

/-!
# Identity-scalar normalization (Pick — unparameterised multi-chart)

`∫(1 • ω, γ) = ∫(ω, γ)` at the user-facing `pathIntegralViaCover`
layer, completing the 6/6 layer tower for `_one_smul` (in-chart
provisional/corrected, via-chart provisional/corrected, cover-with,
Pick).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Identity-scalar normalization (Pick / unparameterised multi-chart). -/
theorem pathIntegralViaCover_one_smul
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover ((1 : ℂ) • ω) γ =
      pathIntegralViaCover ω γ := by
  rw [pathIntegralViaCover_smul, one_smul]

end JacobianChallenge.Periods
