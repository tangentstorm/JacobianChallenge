import Jacobian.Periods.ChartedFormPullbackApply
import Jacobian.Periods.ChartedFormPullbackApplyLinear

/-!
# Pointwise vector-apply forms of `chartedFormPullback` linearity

Vector-apply forms (`e v`) of the existing point-apply linearity
lemmas. Useful when explicitly evaluating the chart-pullback at a
tangent vector.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Vector-apply form: chart pullback of zero is zero. -/
@[simp] theorem chartedFormPullback_zero_apply_apply
    (c : OpenPartialHomeomorph X E) (e v : E) :
    chartedFormPullback c (0 : HolomorphicOneForm E X) e v = 0 := by
  rw [chartedFormPullback_zero_apply]; rfl

/-- Vector-apply form: chart pullback of `-ω` negates pointwise. -/
@[simp] theorem chartedFormPullback_neg_apply_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullback c (-ω) e v = - (chartedFormPullback c ω e v) := by
  rw [chartedFormPullback_neg_apply]; rfl

/-- Vector-apply form: chart pullback distributes over addition. -/
@[simp] theorem chartedFormPullback_add_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullback c (ω + η) e v =
      chartedFormPullback c ω e v + chartedFormPullback c η e v := by
  rw [chartedFormPullback_add_apply]; rfl

/-- Vector-apply form: chart pullback distributes over subtraction. -/
@[simp] theorem chartedFormPullback_sub_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullback c (ω - η) e v =
      chartedFormPullback c ω e v - chartedFormPullback c η e v := by
  rw [chartedFormPullback_sub_apply]; rfl

/-- Vector-apply form: chart pullback is ℂ-linear pointwise. -/
@[simp] theorem chartedFormPullback_smul_apply_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullback c (k • ω) e v = k • (chartedFormPullback c ω e v) := by
  rw [chartedFormPullback_smul_apply]; rfl

end JacobianChallenge.Periods
