import Jacobian.Periods.ChartedFormPullbackEqChartedFormOfMfderivId

/-!
# Set-restricted bridge: `chartedFormPullback = chartedForm` on a set

When `mfderiv c.symm` is the identity at every point of a set
`s ⊆ E`, the corrected and provisional chart-forms agree pointwise
on `s`. This is the most natural intermediate between the global
hypothesis and the per-point bridge — it's exactly what's needed
when `c.symm` only behaves like the chart inverse on `c.target`.
-/

namespace JacobianChallenge.Periods

open Set JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Set-restricted bridge: if `mfderiv c.symm = id` on every `e ∈ s`,
the corrected and provisional chart-forms agree pointwise on `s`.
-/
theorem chartedFormPullback_eqOn_chartedForm_of_mfderiv_id
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) {s : Set E}
    (hd : ∀ e ∈ s, mfderiv (modelWithCornersSelf ℂ E)
                           (modelWithCornersSelf ℂ E) c.symm e =
                   ContinuousLinearMap.id ℂ E) :
    EqOn (chartedFormPullback c ω) (chartedForm c ω) s := fun e he =>
  chartedFormPullback_eq_chartedForm_of_mfderiv_id c ω e (hd e he)

end JacobianChallenge.Periods
