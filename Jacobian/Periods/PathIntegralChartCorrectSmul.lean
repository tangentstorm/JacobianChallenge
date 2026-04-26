import Jacobian.Periods.PathIntegralChartCorrect
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The corrected chart-local path integral is ℂ-linear in the form. -/
@[simp] theorem pathIntegralInChartCorrect_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (k • ω) γ = k • pathIntegralInChartCorrect c ω γ := by
  show curveIntegral (chartedFormPullback c (k • ω)) γ =
       k • curveIntegral (chartedFormPullback c ω) γ
  have h : chartedFormPullback c (k • ω) = k • chartedFormPullback c ω := by
    funext e
    show ((k • ω).toFun (c.symm e)).comp
           (mfderiv (modelWithCornersSelf ℂ E)
                    (modelWithCornersSelf ℂ E) c.symm e) = _
    have hcoe : ((k • ω) : ∀ x, _) (c.symm e) = k • (ω : ∀ x, _) (c.symm e) := by
      rw [ContMDiffSection.coe_smul]
      rfl
    rw [show (k • ω).toFun (c.symm e) = k • (ω.toFun (c.symm e)) from hcoe]
    exact ContinuousLinearMap.smul_comp _ _ _
  rw [h, curveIntegral_smul]

end JacobianChallenge.Periods
