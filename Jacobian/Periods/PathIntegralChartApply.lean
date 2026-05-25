import Jacobian.Periods.PathIntegralChart

/-!
# Definitional unfolding of the provisional `pathIntegralInChart`

A `rfl`-style simp lemma exposing the underlying `curveIntegral` of
`chartedForm`. Mirrors `PathIntegralChartCorrectApply.lean` at the
corrected layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
The provisional chart-local path integral unfolds to
`curveIntegral` of `chartedForm`.
-/
@[simp]
theorem pathIntegralInChart_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c ω γ =
      curveIntegral (chartedForm c ω) γ := rfl

end JacobianChallenge.Periods
