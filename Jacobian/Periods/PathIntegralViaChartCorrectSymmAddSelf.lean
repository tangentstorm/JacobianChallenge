import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Round-trip integral is zero (single-chart, corrected)

The "round-trip" identity: integrating `ω` along `γ` and then along
`γ.symm` cancels, so the sum is `0`. Direct corollary of
`pathIntegralViaChartCorrect_symm` plus `neg_add_cancel`.

Geometrically: traversing a path and then traversing its reverse
returns to the start, and a 1-form integrated over a closed-up
out-and-back loop is zero (which is a special case of Stokes).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Round-trip cancellation (single-chart, corrected): the integral
of `ω` along `γ` plus the integral along `γ.symm` is zero. -/
theorem pathIntegralViaChartCorrect_add_symm_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ h +
        pathIntegralViaChartCorrect c ω γ.symm h' = 0 := by
  rw [pathIntegralViaChartCorrect_symm c ω γ h h', add_neg_cancel]

end JacobianChallenge.Periods
