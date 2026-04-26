import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Scalar-multiplication linearity of the unparameterised multi-chart integral

The `Classical.choose`-picked partition data depends only on `γ`
(and the charted-space structure), NOT on `ω`.  So both sides of
the equation use the SAME picked partition, and the parameterised
`pathIntegralViaCoverWith_smul` applies directly.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The unparameterised multi-chart integral is ℂ-linear in the
form. -/
@[simp] theorem pathIntegralViaCover_smul
    (k : ℂ) (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (k • ω) γ = k • pathIntegralViaCover ω γ := by
  unfold pathIntegralViaCover
  exact pathIntegralViaCoverWith_smul _ _ _ _ _ _ _

end JacobianChallenge.Periods
