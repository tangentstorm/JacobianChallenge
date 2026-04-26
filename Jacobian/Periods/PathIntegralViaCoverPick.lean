import Jacobian.Periods.PathIntegralViaCover

/-!
# Multi-chart path integral with picked partition

The unparameterised wrapper `pathIntegralViaCover ω γ` around
`pathIntegralViaCoverWith`: pick a uniform chart-cover partition via
`exists_uniform_chart_partition` (using `Classical.choose`) and
delegate.

Well-definedness — independence from the picked partition — is a
deferred follow-up. As a consequence, simp lemmas at this level (like
`pathIntegralViaCover_zero`) cannot use the parameterised
`pathIntegralViaCoverWith_zero` directly without unwinding the
`Classical.choose` data; they live on the parameterised version
until well-definedness is proven.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The multi-chart path integral of a holomorphic 1-form along a
path, picking a uniform chart-cover partition via
`exists_uniform_chart_partition`. -/
noncomputable def pathIntegralViaCover
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) : ℂ :=
  let h0 := exists_uniform_chart_partition E γ.toContinuousMap
  let h1 := h0.choose_spec
  let h2 := h1.choose_spec
  pathIntegralViaCoverWith ω γ h0.choose h1.choose h2.choose h2.choose_spec

end JacobianChallenge.Periods
