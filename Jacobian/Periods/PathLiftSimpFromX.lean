import Jacobian.Periods.PathLift

/-!
# chartLift simp lemma for constant paths

The chart-lift of `Path.refl a` through a chart `c` is `Path.refl (c a)`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/-- The chart-lift of a constant path is the constant path on the
chart-image of the point. -/
@[simp] theorem chartLift_refl
    (c : OpenPartialHomeomorph X E) (a : X)
    (h : range (Path.refl a) ⊆ c.source) :
    chartLift c (Path.refl a) h = Path.refl (c a) := by
  apply Path.ext
  funext s
  rfl

end JacobianChallenge.Periods
