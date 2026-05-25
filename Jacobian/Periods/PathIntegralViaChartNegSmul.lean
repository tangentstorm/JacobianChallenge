import Jacobian.Periods.PathIntegralViaChartLinear

/-!
# Provisional via-chart: form-negation factors through scalar negation

Provisional from-`X` analogue of
`pathIntegralViaChartCorrect_neg_smul`. Completes the `_neg_smul`
family across all five layers.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form-negation of a scalar multiple equals the negated scalar
multiple of the integral (provisional from-`X`).
-/
theorem pathIntegralViaChart_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (-(k • ω)) γ h =
      (-k) • pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_neg, pathIntegralViaChart_smul, ← neg_smul]

end JacobianChallenge.Periods
