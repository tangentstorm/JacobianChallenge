import Jacobian.Periods.PathIntegralChartCorrectSimp

/-!
In-chart corrected analogue of `pathIntegralViaChartCorrect_add_symm_self`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
`pathIntegralInChartCorrect c ω γ + pathIntegralInChartCorrect c ω γ.symm = 0`.

1-line `rw` corollary combining the in-chart corrected `_symm`
with `add_neg_cancel`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]


theorem pathIntegralInChartCorrect_add_symm_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c ω γ +
        pathIntegralInChartCorrect c ω γ.symm = 0 := by
  rw [pathIntegralInChartCorrect_symm, add_neg_cancel]

end JacobianChallenge.Periods
