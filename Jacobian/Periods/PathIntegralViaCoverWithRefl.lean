import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.ChartLiftReflSubpath
import Jacobian.Periods.PathIntegralChartCorrectSimp
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Multi-chart path integral over a constant path is zero

The integrand on each segment is `pathIntegralViaChartCorrect` applied
to a subpath of the constant path; we use `chartLift_refl_subpath` to
rewrite the chart-lifted path to `Path.refl (c a)`, then
`curveIntegral_refl` closes each segment.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The multi-chart path integral over a constant path is zero. -/
@[simp] theorem pathIntegralViaCoverWith_refl
    (ω : HolomorphicOneForm E X) (a : X)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      (Path.refl a) t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ω (Path.refl a) n hn pickChart hcov = 0 := by
  unfold pathIntegralViaCoverWith
  apply Finset.sum_eq_zero
  intro i _
  show pathIntegralInChartCorrect _ ω
        (chartLift _ ((Path.refl a).subpath _ _) _) = 0
  rw [chartLift_refl_subpath]
  exact pathIntegralInChartCorrect_refl _ _ _

end JacobianChallenge.Periods
