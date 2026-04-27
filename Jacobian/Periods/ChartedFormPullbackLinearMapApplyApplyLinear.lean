import Jacobian.Periods.ChartedFormPullbackLinearMapApplyLinear
import Jacobian.Periods.ChartedFormPullbackApplyApplyLinear

/-!
# Bundled vector-apply linearity for `chartedFormPullbackLinearMap`

Vector-apply (`e v`) forms of the bundled-LinearMap-level linearity
simp lemmas. Lifted from the unbundled vector-apply forms via
`chartedFormPullbackLinearMap_apply_at`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Bundled vector-apply: zero form. -/
@[simp] theorem chartedFormPullbackLinearMap_zero_apply_apply
    (c : OpenPartialHomeomorph X E) (e v : E) :
    chartedFormPullbackLinearMap c (0 : HolomorphicOneForm E X) e v = 0 := by
  rw [chartedFormPullbackLinearMap_zero_apply]; rfl

/-- Bundled vector-apply: negation. -/
@[simp] theorem chartedFormPullbackLinearMap_neg_apply_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullbackLinearMap c (-ω) e v =
      - (chartedFormPullbackLinearMap c ω e v) := by
  rw [chartedFormPullbackLinearMap_neg_apply]; rfl

/-- Bundled vector-apply: addition. -/
@[simp] theorem chartedFormPullbackLinearMap_add_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullbackLinearMap c (ω + η) e v =
      chartedFormPullbackLinearMap c ω e v +
        chartedFormPullbackLinearMap c η e v := by
  rw [chartedFormPullbackLinearMap_add_apply]; rfl

/-- Bundled vector-apply: subtraction. -/
@[simp] theorem chartedFormPullbackLinearMap_sub_apply_apply
    (c : OpenPartialHomeomorph X E) (ω η : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullbackLinearMap c (ω - η) e v =
      chartedFormPullbackLinearMap c ω e v -
        chartedFormPullbackLinearMap c η e v := by
  rw [chartedFormPullbackLinearMap_sub_apply]; rfl

/-- Bundled vector-apply: scalar multiplication. -/
@[simp] theorem chartedFormPullbackLinearMap_smul_apply_apply
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X) (e v : E) :
    chartedFormPullbackLinearMap c (k • ω) e v =
      k • (chartedFormPullbackLinearMap c ω e v) := by
  rw [chartedFormPullbackLinearMap_smul_apply]; rfl

end JacobianChallenge.Periods
