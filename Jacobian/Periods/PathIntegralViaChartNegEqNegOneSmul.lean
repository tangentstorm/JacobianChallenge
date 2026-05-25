import Jacobian.Periods.PathIntegralViaChartLinear

/-!
# Form negation as scalar multiplication by `-1` (provisional via-chart)

Provisional via-chart layer of `_neg_eq_neg_one_smul`, completing
the bridge across all five layers.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Form negation equals `(-1) •` on the integral
(provisional via-chart).
-/
theorem pathIntegralViaChart_neg_eq_neg_one_smul
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (-ω) γ h =
      (-1 : ℂ) • pathIntegralViaChart c ω γ h := by
  rw [pathIntegralViaChart_neg, neg_one_smul]

end JacobianChallenge.Periods
