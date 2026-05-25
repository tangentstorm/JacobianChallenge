import Jacobian.Periods.ChartedFormPullback
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/--
Chart-local path integral using the genuine chart pullback
`chartedFormPullback` (includes the `mfderiv` factor of `c.symm`).

Compare with the provisional `pathIntegralInChart c ω γ` in
`Jacobian/Periods/PathIntegralChart.lean`, which uses the simpler
`chartedForm` (no derivative factor); that version coincides with
this one only when chart transitions are translations.
-/
noncomputable def pathIntegralInChartCorrect
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X)
    {a b : E}
    (γ : Path a b) : ℂ :=
  curveIntegral (chartedFormPullback c ω) γ

end JacobianChallenge.Periods
