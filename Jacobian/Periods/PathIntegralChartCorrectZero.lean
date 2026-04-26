import Jacobian.Periods.PathIntegralChartCorrect
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The corrected chart-local path integral of the zero form is `0`. -/
@[simp] theorem pathIntegralInChartCorrect_zero
    (c : OpenPartialHomeomorph X E) {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (0 : HolomorphicOneForm E X) γ = 0 := by
  show curveIntegral (chartedFormPullback c 0) γ = 0
  have h : chartedFormPullback c (0 : HolomorphicOneForm E X) = 0 := by
    funext e
    show ((0 : HolomorphicOneForm E X).toFun (c.symm e)).comp
           (mfderiv (modelWithCornersSelf ℂ E)
                    (modelWithCornersSelf ℂ E) c.symm e) = 0
    have hcoe : ((0 : HolomorphicOneForm E X) : ∀ x, _) (c.symm e) = 0 := by
      rw [ContMDiffSection.coe_zero]
      rfl
    rw [show (0 : HolomorphicOneForm E X).toFun (c.symm e) = 0 from hcoe]
    exact ContinuousLinearMap.zero_comp _
  rw [h, curveIntegral_zero]

end JacobianChallenge.Periods
