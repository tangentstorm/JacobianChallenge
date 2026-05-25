import Jacobian.Periods.PathLift
import Jacobian.Periods.PathReflSubpath
import Mathlib.Topology.Subpath

/-!
# Chart-lift of a subpath of a constant path

The chart-lift of any subpath of `Path.refl a` is `Path.refl (c a)`.
This sidesteps the dependent-range-rewrite issue encountered when
trying to prove `pathIntegralViaCoverWith_refl` directly.
-/

namespace JacobianChallenge.Periods

open Set JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/--
The chart-lift of a subpath of a constant path is the constant
path on the chart-image of the point.
-/
theorem chartLift_refl_subpath
    (c : OpenPartialHomeomorph X E) (a : X) (t₀ t₁ : unitInterval)
    (h : range ((Path.refl a).subpath t₀ t₁) ⊆ c.source) :
    chartLift c ((Path.refl a).subpath t₀ t₁) h = Path.refl (c a) := by
  apply Path.ext
  funext s
  rfl

end JacobianChallenge.Periods
