import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverZero
import Jacobian.Periods.PathIntegralViaCoverNeg

/-!
# Linearity of the unparameterised multi-chart integral

The `Classical.choose`-picked partition data depends only on `γ`
(and the charted-space structure), NOT on `ω`.  So both sides of
each linearity equation use the SAME picked partition, and the
parameterised `pathIntegralViaCoverWith_*` lemmas apply directly.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The unparameterised multi-chart integral of the zero form is zero. -/
@[simp] theorem pathIntegralViaCover_zero
    {a b : X} (γ : Path a b) :
    pathIntegralViaCover (0 : HolomorphicOneForm E X) γ = 0 := by
  unfold pathIntegralViaCover
  exact pathIntegralViaCoverWith_zero _ _ _ _ _

/-- The unparameterised multi-chart integral negates with the form. -/
@[simp] theorem pathIntegralViaCover_neg
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (-ω) γ = - pathIntegralViaCover ω γ := by
  unfold pathIntegralViaCover
  exact pathIntegralViaCoverWith_neg _ _ _ _ _ _

end JacobianChallenge.Periods
