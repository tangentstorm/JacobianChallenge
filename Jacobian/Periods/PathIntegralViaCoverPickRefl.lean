import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverWithRefl

/-!
# Constant-path vanishing for the unparameterised multi-chart integral

The `Classical.choose`-picked partition data depends only on `γ`
(and the charted-space structure), NOT on `ω`.  So unfolding
`pathIntegralViaCover` reduces directly to
`pathIntegralViaCoverWith_refl`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The unparameterised multi-chart integral over a constant path
is zero. -/
@[simp] theorem pathIntegralViaCover_refl
    (ω : HolomorphicOneForm E X) (a : X) :
    pathIntegralViaCover ω (Path.refl a) = 0 := by
  unfold pathIntegralViaCover
  exact pathIntegralViaCoverWith_refl _ _ _ _ _ _

end JacobianChallenge.Periods
