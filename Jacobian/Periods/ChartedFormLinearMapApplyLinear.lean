import Jacobian.Periods.ChartedFormLinearMapApply
import Jacobian.Periods.ChartedFormLinearMapSimp
import Jacobian.Periods.ChartedFormLinearMapSmul
import Jacobian.Periods.ChartedFormApplyLinear

/-!
# Pointwise apply forms of the bundled provisional `chartedFormLinearMap` linearity

Provisional analogue of `ChartedFormPullbackLinearMapApplyLinear.lean`
at the corrected layer. Each lemma delegates through
`chartedFormLinearMap_apply_at` (the rfl-bridge to the unbundled
`chartedForm`) to the apply-form bundle in
`ChartedFormApplyLinear.lean`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pointwise apply form: bundled provisional chart-form of zero is zero CLM. -/
@[simp] theorem chartedFormLinearMap_zero_apply
    (c : OpenPartialHomeomorph X E) (e : E) :
    chartedFormLinearMap c (0 : HolomorphicOneForm E X) e = 0 := by
  rw [chartedFormLinearMap_apply_at, chartedForm_zero_apply]

/-- Pointwise apply form: bundled provisional chart-form negates pointwise. -/
@[simp] theorem chartedFormLinearMap_neg_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormLinearMap c (-ω) e =
      - chartedFormLinearMap c ω e := by
  rw [chartedFormLinearMap_apply_at, chartedFormLinearMap_apply_at,
      chartedForm_neg_apply]

/-- Pointwise apply form: bundled provisional chart-form distributes over addition. -/
@[simp] theorem chartedFormLinearMap_add_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormLinearMap c (ω + η) e =
      chartedFormLinearMap c ω e + chartedFormLinearMap c η e := by
  rw [chartedFormLinearMap_apply_at, chartedFormLinearMap_apply_at,
      chartedFormLinearMap_apply_at, chartedForm_add_apply]

/-- Pointwise apply form: bundled provisional chart-form distributes over subtraction. -/
@[simp] theorem chartedFormLinearMap_sub_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormLinearMap c (ω - η) e =
      chartedFormLinearMap c ω e - chartedFormLinearMap c η e := by
  rw [chartedFormLinearMap_apply_at, chartedFormLinearMap_apply_at,
      chartedFormLinearMap_apply_at, chartedForm_sub_apply]

/-- Pointwise apply form: bundled provisional chart-form is ℂ-linear pointwise. -/
@[simp] theorem chartedFormLinearMap_smul_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormLinearMap c (k • ω) e =
      k • chartedFormLinearMap c ω e := by
  rw [chartedFormLinearMap_apply_at, chartedFormLinearMap_apply_at,
      chartedForm_smul_apply]

end JacobianChallenge.Periods
