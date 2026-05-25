import Jacobian.Periods.PathIntegralViaCoverPick

/-!
# Definitional unfolding of `pathIntegralViaCover`

Shows that `pathIntegralViaCover` reduces to `pathIntegralViaCoverWith`
applied to the `Classical.choose`-picked partition data from
`exists_uniform_chart_partition`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
The unparameterised `pathIntegralViaCover` reduces to
`pathIntegralViaCoverWith` applied to the `Classical.choose`-picked
partition data.
-/
theorem pathIntegralViaCover_eq_pathIntegralViaCoverWith
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover ω γ =
      pathIntegralViaCoverWith ω γ
        (exists_uniform_chart_partition E γ.toContinuousMap).choose
        (exists_uniform_chart_partition E γ.toContinuousMap).choose_spec.choose
        (exists_uniform_chart_partition E γ.toContinuousMap).choose_spec.choose_spec.choose
        (exists_uniform_chart_partition E γ.toContinuousMap).choose_spec.choose_spec.choose_spec := rfl

end JacobianChallenge.Periods
