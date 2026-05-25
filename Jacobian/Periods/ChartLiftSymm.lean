import Jacobian.Periods.PathLift

/-!
# `chartLift` commutes with `Path.symm`

`chartLift c γ.symm h' = (chartLift c γ h).symm`. Both sides are
defined as the composition `c ∘ γ ∘ σ` (where `σ = unitInterval.symm`),
just with different bracketings — `Path.symm` factors out the `σ` on
the path side, while `Path.map'` factors out the `c` on the chart
side. The proof is `Path.ext rfl`.

Used by `pathIntegralViaChartCorrect_symm` and (eventually) by the
multi-chart `pathIntegralViaCoverWith_symm`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/--
The chart-lift of a reversed path equals the reverse of the
chart-lifted path.
-/
theorem chartLift_symm
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source)
    (h' : range γ.symm ⊆ c.source) :
    chartLift c γ.symm h' = (chartLift c γ h).symm := by
  unfold chartLift
  exact Path.ext rfl

end JacobianChallenge.Periods
