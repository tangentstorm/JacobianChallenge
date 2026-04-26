import Jacobian.Periods.ChartedFormPullbackApply
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul
import Jacobian.Periods.ChartedFormPullbackSub

/-!
# Pointwise `_apply` forms of the `chartedFormPullback` linearity simp lemmas

The function-level simp lemmas `chartedFormPullback_{zero,neg,add,sub,smul}`
plus the corresponding `Pi.*_apply` lemmas already let `simp` derive the
pointwise versions automatically, but explicit apply-forms are useful for
direct proof-writing with `rw`/`exact` (especially in Aristotle prompts
where we ask for simple tactics).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pointwise apply form: chart pullback of the zero form is the zero CLM. -/
@[simp] theorem chartedFormPullback_zero_apply
    (c : OpenPartialHomeomorph X E) (e : E) :
    chartedFormPullback c (0 : HolomorphicOneForm E X) e = 0 := by
  rw [chartedFormPullback_zero]; rfl

/-- Pointwise apply form: chart pullback of `-ω` negates pointwise. -/
@[simp] theorem chartedFormPullback_neg_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c (-ω) e = - chartedFormPullback c ω e := by
  rw [chartedFormPullback_neg]; rfl

/-- Pointwise apply form: chart pullback distributes over addition. -/
@[simp] theorem chartedFormPullback_add_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c (ω + η) e =
      chartedFormPullback c ω e + chartedFormPullback c η e := by
  rw [chartedFormPullback_add]; rfl

/-- Pointwise apply form: chart pullback distributes over subtraction. -/
@[simp] theorem chartedFormPullback_sub_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c (ω - η) e =
      chartedFormPullback c ω e - chartedFormPullback c η e := by
  rw [chartedFormPullback_sub]; rfl

/-- Pointwise apply form: chart pullback is ℂ-linear pointwise. -/
@[simp] theorem chartedFormPullback_smul_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c (k • ω) e = k • chartedFormPullback c ω e := by
  rw [chartedFormPullback_smul]; rfl

end JacobianChallenge.Periods
