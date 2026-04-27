import Jacobian.Periods.PathIntegralViaCoverPickSmul

/-!
# Iterated scalar multiplication composes (Pick — unparameterised multi-chart)

`∫(k • (l • ω), γ) = (k * l) • ∫(ω, γ)` at the user-facing
`pathIntegralViaCover` wrapper, completing the 6/6 layer tower for
`_smul_smul`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Iterated scalar multiplication composes
(Pick / unparameterised multi-chart). -/
theorem pathIntegralViaCover_smul_smul
    (k l : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) :
    pathIntegralViaCover (k • (l • ω)) γ =
      (k * l) • pathIntegralViaCover ω γ := by
  rw [pathIntegralViaCover_smul, pathIntegralViaCover_smul, smul_smul]

end JacobianChallenge.Periods
