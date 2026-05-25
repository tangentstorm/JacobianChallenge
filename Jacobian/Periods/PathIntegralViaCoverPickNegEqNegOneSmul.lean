import Jacobian.Periods.PathIntegralViaCoverPickSimp
import Jacobian.Periods.PathIntegralViaCoverPickSmul

/-!
# Form negation as `(-1) •` (Pick — unparameterised multi-chart)

`pathIntegralViaCover (-ω) γ = (-1) • pathIntegralViaCover ω γ` at
the user-facing wrapper, completing the 6/6 layer tower for
`_neg_eq_neg_one_smul` (in-chart provisional/corrected, via-chart
provisional/corrected, cover-with, Pick).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form negation equals `(-1) •` on the integral
(Pick / unparameterised multi-chart).
-/
theorem pathIntegralViaCover_neg_eq_neg_one_smul
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (-ω) γ =
      (-1 : ℂ) • pathIntegralViaCover ω γ := by
  rw [pathIntegralViaCover_neg, neg_one_smul]

end JacobianChallenge.Periods
