import Jacobian.Periods.ChartLiftApply

/-!
# Boundary values of `chartLift`

`chartLift c γ h` is a path in `E` from `c a` to `c b`. Its values at
`0` and `1` reduce to `c a` and `c b` respectively, by combining
`chartLift_apply` (the rfl-bridge to `c (γ s)`) with `Path.source`
(γ 0 = a) and `Path.target` (γ 1 = b).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/-- The chart-lift evaluated at `0` is `c a`. -/
@[simp] theorem chartLift_zero
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    chartLift c γ h 0 = c a := by
  rw [chartLift_apply, γ.source]

/-- The chart-lift evaluated at `1` is `c b`. -/
@[simp] theorem chartLift_one
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    chartLift c γ h 1 = c b := by
  rw [chartLift_apply, γ.target]

end JacobianChallenge.Periods
