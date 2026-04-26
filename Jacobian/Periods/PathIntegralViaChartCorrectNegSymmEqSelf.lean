import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralViaChartCorrectNeg

/-!
# Negate-and-reverse equals self (single-chart, corrected)

`∫(-ω, γ.symm) = ∫(ω, γ)`: negating the form and reversing the
path together cancels both sign flips, returning the original
integral. Direct corollary of `_neg_form_eq_symm_path` plus
`_symm`.

Geometrically: the substitution `t → 1 - t` combined with `ω → -ω`
is the identity on path integrals.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Negate-and-reverse cancellation (single-chart, corrected):
`∫(-ω, γ.symm) = ∫(ω, γ)`. -/
theorem pathIntegralViaChartCorrect_neg_symm_eq_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c (-ω) γ.symm h' =
      pathIntegralViaChartCorrect c ω γ h := by
  rw [pathIntegralViaChartCorrect_symm c (-ω) γ h h',
      pathIntegralViaChartCorrect_neg, neg_neg]

end JacobianChallenge.Periods
