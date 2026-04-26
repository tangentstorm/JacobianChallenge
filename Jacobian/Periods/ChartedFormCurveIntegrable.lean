import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.ChartedFormSmul
import Jacobian.Periods.ChartedFormSub
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Curve integrability of `chartedForm` (provisional layer)

Mirrors `Jacobian/Periods/ChartedFormPullbackCurveIntegrable.lean`
at the corrected layer. Each lemma reduces to the corresponding
`CurveIntegrable.{zero,neg,smul,add,sub}` after rewriting the
`chartedForm c (-ω)` etc. via the function-level simp lemmas.

The full curve-integrability theorem `chartedForm_curveIntegrable`
(unconditional, requires regularity assumptions on the path) is
the provisional analogue of Packet F and is a separate substantive
follow-up.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The provisional chart-form of the zero form is curve-integrable
along any path. -/
theorem chartedForm_zero_curveIntegrable
    (c : OpenPartialHomeomorph X E) {a b : E} (γ : Path a b) :
    CurveIntegrable (chartedForm c (0 : HolomorphicOneForm E X)) γ := by
  rw [chartedForm_zero]
  exact CurveIntegrable.zero

/-- If the provisional chart-form of `ω` is curve-integrable along `γ`,
then so is that of `-ω`. -/
theorem chartedForm_neg_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (h : CurveIntegrable (chartedForm c ω) γ) :
    CurveIntegrable (chartedForm c (-ω)) γ := by
  rw [chartedForm_neg]
  exact h.neg

/-- If the provisional chart-form of `ω` is curve-integrable along `γ`,
then so is that of `k • ω`. -/
theorem chartedForm_smul_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (h : CurveIntegrable (chartedForm c ω) γ) (k : ℂ) :
    CurveIntegrable (chartedForm c (k • ω)) γ := by
  rw [chartedForm_smul]
  exact h.smul

/-- If the provisional chart-forms of `ω` and `η` are both
curve-integrable along `γ`, then so is that of `ω + η`. -/
theorem chartedForm_add_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω η : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (hω : CurveIntegrable (chartedForm c ω) γ)
    (hη : CurveIntegrable (chartedForm c η) γ) :
    CurveIntegrable (chartedForm c (ω + η)) γ := by
  rw [chartedForm_add]
  exact hω.add hη

/-- If the provisional chart-forms of `ω` and `η` are both
curve-integrable along `γ`, then so is that of `ω - η`. -/
theorem chartedForm_sub_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω η : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (hω : CurveIntegrable (chartedForm c ω) γ)
    (hη : CurveIntegrable (chartedForm c η) γ) :
    CurveIntegrable (chartedForm c (ω - η)) γ := by
  rw [chartedForm_sub]
  exact hω.sub hη

end JacobianChallenge.Periods
