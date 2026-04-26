import Jacobian.Periods.ChartedFormPullbackLinearMapApply
import Jacobian.Periods.ChartedFormPullbackLinearMapSimp
import Jacobian.Periods.ChartedFormPullbackLinearMapSmul
import Jacobian.Periods.ChartedFormPullbackApplyLinear

/-!
# Pointwise `_apply` forms of the LinearMap-level linearity simp lemmas

The bundled `chartedFormPullbackLinearMap c` is definitionally equal to
the unbundled `chartedFormPullback c` at every point, so its linearity
behaviour reduces directly to the unbundled apply-form lemmas in
`ChartedFormPullbackApplyLinear.lean`. These five facade lemmas just
expose that fact at the LinearMap level for downstream callers that
work with the bundled form.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pointwise apply form: bundled chart pullback of the zero form is the zero CLM. -/
@[simp] theorem chartedFormPullbackLinearMap_zero_apply
    (c : OpenPartialHomeomorph X E) (e : E) :
    chartedFormPullbackLinearMap c (0 : HolomorphicOneForm E X) e = 0 := by
  rw [chartedFormPullbackLinearMap_apply_at, chartedFormPullback_zero_apply]

/-- Pointwise apply form: bundled chart pullback of `-ω` negates pointwise. -/
@[simp] theorem chartedFormPullbackLinearMap_neg_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullbackLinearMap c (-ω) e =
      - chartedFormPullbackLinearMap c ω e := by
  rw [chartedFormPullbackLinearMap_apply_at, chartedFormPullbackLinearMap_apply_at,
      chartedFormPullback_neg_apply]

/-- Pointwise apply form: bundled chart pullback distributes over addition. -/
@[simp] theorem chartedFormPullbackLinearMap_add_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormPullbackLinearMap c (ω + η) e =
      chartedFormPullbackLinearMap c ω e + chartedFormPullbackLinearMap c η e := by
  rw [chartedFormPullbackLinearMap_apply_at, chartedFormPullbackLinearMap_apply_at,
      chartedFormPullbackLinearMap_apply_at, chartedFormPullback_add_apply]

/-- Pointwise apply form: bundled chart pullback distributes over subtraction. -/
@[simp] theorem chartedFormPullbackLinearMap_sub_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e : E) :
    chartedFormPullbackLinearMap c (ω - η) e =
      chartedFormPullbackLinearMap c ω e - chartedFormPullbackLinearMap c η e := by
  rw [chartedFormPullbackLinearMap_apply_at, chartedFormPullbackLinearMap_apply_at,
      chartedFormPullbackLinearMap_apply_at, chartedFormPullback_sub_apply]

/-- Pointwise apply form: bundled chart pullback is ℂ-linear pointwise. -/
@[simp] theorem chartedFormPullbackLinearMap_smul_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullbackLinearMap c (k • ω) e =
      k • chartedFormPullbackLinearMap c ω e := by
  rw [chartedFormPullbackLinearMap_apply_at, chartedFormPullbackLinearMap_apply_at,
      chartedFormPullback_smul_apply]

end JacobianChallenge.Periods
