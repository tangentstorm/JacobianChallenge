import Jacobian.Periods.PathLift

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/-- Pointwise value of the chart-lift of a path. -/
@[simp] theorem chartLift_apply
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) (s : unitInterval) :
    chartLift c γ h s = c (γ s) := rfl

end JacobianChallenge.Periods
