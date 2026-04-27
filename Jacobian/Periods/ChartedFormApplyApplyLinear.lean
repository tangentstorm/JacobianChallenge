import Jacobian.Periods.ChartedFormApplyLinear

/-!
# Pointwise vector-apply forms of `chartedForm` linearity (provisional)

Vector-apply forms (`e v`) of the existing point-apply linearity
lemmas at the provisional `chartedForm` layer. Mirrors the corrected
`ChartedFormPullbackApplyApplyLinear.lean`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Vector-apply form: provisional chart-form of zero is zero. -/
@[simp] theorem chartedForm_zero_apply_apply
    (c : OpenPartialHomeomorph X E) (e v : E) :
    chartedForm c (0 : HolomorphicOneForm E X) e v = 0 := by
  rw [chartedForm_zero_apply]; rfl

/-- Vector-apply form: provisional chart-form of `-ω` negates pointwise. -/
@[simp] theorem chartedForm_neg_apply_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedForm c (-ω) e v = - (chartedForm c ω e v) := by
  rw [chartedForm_neg_apply]; rfl

/-- Vector-apply form: provisional chart-form distributes over addition. -/
@[simp] theorem chartedForm_add_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedForm c (ω + η) e v = chartedForm c ω e v + chartedForm c η e v := by
  rw [chartedForm_add_apply]; rfl

/-- Vector-apply form: provisional chart-form distributes over subtraction. -/
@[simp] theorem chartedForm_sub_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedForm c (ω - η) e v = chartedForm c ω e v - chartedForm c η e v := by
  rw [chartedForm_sub_apply]; rfl

/-- Vector-apply form: provisional chart-form is ℂ-linear pointwise. -/
@[simp] theorem chartedForm_smul_apply_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedForm c (k • ω) e v = k • (chartedForm c ω e v) := by
  rw [chartedForm_smul_apply]; rfl

end JacobianChallenge.Periods
