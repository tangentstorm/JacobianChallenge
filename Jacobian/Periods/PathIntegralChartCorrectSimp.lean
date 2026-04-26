import Jacobian.Periods.PathIntegralChartCorrect
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The corrected chart-local path integral over a constant path is `0`. -/
@[simp] theorem pathIntegralInChartCorrect_refl
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (a : E) :
    pathIntegralInChartCorrect c ω (Path.refl a) = 0 :=
  curveIntegral_refl _ a

/-- The corrected chart-local path integral reverses sign under path symmetry. -/
theorem pathIntegralInChartCorrect_symm
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c ω γ.symm =
      - pathIntegralInChartCorrect c ω γ :=
  curveIntegral_symm _ γ

end JacobianChallenge.Periods
