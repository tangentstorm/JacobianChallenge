import Jacobian.Periods.PathLift

/-!
# Definitional unfolding of the provisional `pathIntegralViaChart`

A `rfl`-style simp lemma exposing the from-`X` integral as the
in-chart integral on the chart-lifted path. Mirrors
`PathIntegralViaChartCorrectApply.lean` at the corrected layer.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
The provisional from-`X` chart-local path integral unfolds to
the in-chart integral on the chart-lifted path.
-/
@[simp]
theorem pathIntegralViaChart_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c ω γ h =
      pathIntegralInChart c ω (chartLift c γ h) := rfl

end JacobianChallenge.Periods
