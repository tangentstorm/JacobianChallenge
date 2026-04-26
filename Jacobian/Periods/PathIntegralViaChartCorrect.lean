import Jacobian.Periods.PathLift
import Jacobian.Periods.ChartLiftSymm
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectSimp

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- From-`X` corrected chart-local path integral: lift the path
through the chart and integrate using the genuine chart pullback. -/
noncomputable def pathIntegralViaChartCorrect
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) : ℂ :=
  pathIntegralInChartCorrect c ω (chartLift c γ h)

/-- Constant path: corrected from-`X` integral is zero. -/
@[simp] theorem pathIntegralViaChartCorrect_refl
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (a : X)
    (h : range (Path.refl a) ⊆ c.source) :
    pathIntegralViaChartCorrect c ω (Path.refl a) h = 0 := by
  unfold pathIntegralViaChartCorrect chartLift
  have : (Path.refl a).map' (c.continuousOn_toFun.mono h) = Path.refl (c a) :=
    Path.ext rfl
  rw [this]
  exact pathIntegralInChartCorrect_refl c ω (c a)

/-- Symmetric path: corrected from-`X` integral negates. -/
theorem pathIntegralViaChartCorrect_symm
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source)
    (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ.symm h' =
      - pathIntegralViaChartCorrect c ω γ h := by
  unfold pathIntegralViaChartCorrect
  rw [chartLift_symm c γ h h']
  exact pathIntegralInChartCorrect_symm c ω (chartLift c γ h)

end JacobianChallenge.Periods
