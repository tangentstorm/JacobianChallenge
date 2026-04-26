import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.ChartedFormSmul
import Jacobian.Periods.ChartedFormSub

/-!
# Pointwise `_apply` forms of the provisional `chartedForm` linearity simps

Mirrors `Jacobian/Periods/ChartedFormPullbackApplyLinear.lean` at
the corrected layer. The function-level simps plus `Pi.*_apply`
already let `simp` derive the pointwise versions, but explicit
apply-forms are useful for direct `rw`/`exact` proofs.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pointwise apply form: provisional chart-form of zero is zero CLM. -/
@[simp] theorem chartedForm_zero_apply
    (c : OpenPartialHomeomorph X E) (e : E) :
    chartedForm c (0 : HolomorphicOneForm E X) e = 0 := by
  rw [chartedForm_zero]; rfl

/-- Pointwise apply form: provisional chart-form negates pointwise. -/
@[simp] theorem chartedForm_neg_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedForm c (-ω) e = - chartedForm c ω e := by
  rw [chartedForm_neg]; rfl

/-- Pointwise apply form: provisional chart-form distributes over addition. -/
@[simp] theorem chartedForm_add_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedForm c (ω + η) e = chartedForm c ω e + chartedForm c η e := by
  rw [chartedForm_add]; rfl

/-- Pointwise apply form: provisional chart-form distributes over subtraction. -/
@[simp] theorem chartedForm_sub_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedForm c (ω - η) e = chartedForm c ω e - chartedForm c η e := by
  rw [chartedForm_sub]; rfl

/-- Pointwise apply form: provisional chart-form is ℂ-linear pointwise. -/
@[simp] theorem chartedForm_smul_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e : E) :
    chartedForm c (k • ω) e = k • chartedForm c ω e := by
  rw [chartedForm_smul]; rfl

end JacobianChallenge.Periods
