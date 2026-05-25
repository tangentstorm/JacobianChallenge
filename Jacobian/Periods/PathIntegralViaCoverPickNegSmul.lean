import Jacobian.Periods.PathIntegralViaCoverPickSimp
import Jacobian.Periods.PathIntegralViaCoverPickSmul

/-!
# Form-negation of a scalar multiple (Pick — unparameterised multi-chart)

`∫(-(k • ω), γ) = (-k) • ∫(ω, γ)` at the user-facing
`pathIntegralViaCover` wrapper, completing the 6/6 layer tower for
`_neg_smul`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form-negation of a scalar multiple equals the negated scalar
multiple of the integral (Pick / unparameterised multi-chart).
-/
theorem pathIntegralViaCover_neg_smul
    (k : ℂ) (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (-(k • ω)) γ =
      (-k) • pathIntegralViaCover ω γ := by
  rw [pathIntegralViaCover_neg, pathIntegralViaCover_smul, ← neg_smul]

end JacobianChallenge.Periods
