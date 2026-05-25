import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
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


theorem pathIntegralViaChartCorrect_add_symm_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ h +
        pathIntegralViaChartCorrect c ω γ.symm h' = 0 := by
  rw [pathIntegralViaChartCorrect_symm c ω γ h h', add_neg_cancel]

end JacobianChallenge.Periods
