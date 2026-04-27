import Jacobian.Periods.ChartedFormLinearMapApplyLinear
import Jacobian.Periods.ChartedFormApplyApplyLinear

/-!
# Bundled vector-apply linearity for provisional `chartedFormLinearMap`

Vector-apply (`e v`) forms of the bundled provisional-chart-form
linearity simp lemmas. Lifted from the unbundled vector-apply forms
via `chartedFormLinearMap_apply_at`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Bundled provisional vector-apply: zero form. -/
@[simp] theorem chartedFormLinearMap_zero_apply_apply
    (c : OpenPartialHomeomorph X E) (e v : E) :
    chartedFormLinearMap c (0 : HolomorphicOneForm E X) e v = 0 := by
  rw [chartedFormLinearMap_zero_apply]; rfl

/-- Bundled provisional vector-apply: negation. -/
@[simp] theorem chartedFormLinearMap_neg_apply_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormLinearMap c (-ω) e v =
      - (chartedFormLinearMap c ω e v) := by
  rw [chartedFormLinearMap_neg_apply]; rfl

/-- Bundled provisional vector-apply: addition. -/
@[simp] theorem chartedFormLinearMap_add_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormLinearMap c (ω + η) e v =
      chartedFormLinearMap c ω e v +
        chartedFormLinearMap c η e v := by
  rw [chartedFormLinearMap_add_apply]; rfl

/-- Bundled provisional vector-apply: subtraction. -/
@[simp] theorem chartedFormLinearMap_sub_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormLinearMap c (ω - η) e v =
      chartedFormLinearMap c ω e v -
        chartedFormLinearMap c η e v := by
  rw [chartedFormLinearMap_sub_apply]; rfl

/-- Bundled provisional vector-apply: scalar multiplication. -/
@[simp] theorem chartedFormLinearMap_smul_apply_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormLinearMap c (k • ω) e v =
      k • (chartedFormLinearMap c ω e v) := by
  rw [chartedFormLinearMap_smul_apply]; rfl

end JacobianChallenge.Periods
